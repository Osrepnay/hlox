module Parser where
 --(exprP) where

import           Control.Applicative     hiding ( many
                                                , some
                                                )
import           Control.Monad.Combinators.Expr
import           Data.Functor
import           Data.Maybe
import           Data.Text                      ( Text )
import qualified Data.Text                     as T
import           Data.Void
import           Text.Megaparsec
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer    as L

type Parser = Parsec Void Text

data WithOffset a = WithOffset a Int
    deriving Show
instance Functor WithOffset where
    fmap f (WithOffset a o) = WithOffset (f a) o

type DeclO = WithOffset Decl
type VarDeclarationO = WithOffset VarDeclaration
type StmtO = WithOffset Stmt
type ExprO = WithOffset Expr
type LiteralO = WithOffset Literal
type IdentifierO = WithOffset Identifier
type BinaryOpO = WithOffset BinaryOp
type UnaryOpO = WithOffset UnaryOp

data Decl = StmtD Stmt | VarDecl VarDeclaration deriving Show
-- same as assignment
data VarDeclaration = VarDeclaration IdentifierO ExprO deriving Show
data Stmt = ExprStmt Expr
          | Print ExprO
          | Block [DeclO]
          | Cont Control
          | ReturnStmt ExprO
          deriving Show
data Expr = Lit Literal
          | BinOp ExprO BinaryOpO ExprO
          | UnOp UnaryOpO ExprO
          | Ident Identifier
          | Assign IdentifierO ExprO
          | Call ExprO [ExprO]
          deriving Show

data Literal = BoolLit Bool | NumLit Double | StrLit String | Func [DeclO] | Nil deriving Show
type Identifier = String
data BinaryOp = Plus | Minus | Times | Div | Eq | NEq | Lt | Gt | LtE | GtE | Or | And deriving Show
data UnaryOp = Neg | Not deriving Show
data Control = If ExprO StmtO (Maybe StmtO) | While ExprO StmtO deriving Show

unOffset :: WithOffset a -> a
unOffset (WithOffset x _) = x

withLocation :: Parser a -> Parser (WithOffset a)
withLocation = liftA2 (flip WithOffset) getOffset

spaceP :: Parser ()
spaceP = L.space space1 (L.skipLineComment (T.pack "//")) empty

lexeme :: Parser a -> Parser a
lexeme = L.lexeme spaceP

symbol :: String -> Parser Text
symbol = L.symbol spaceP . T.pack

stringStandalone :: String -> Parser Text
stringStandalone = lexeme . (<* notFollowedBy alphaNumChar) . string . T.pack

charLexeme :: Char -> Parser Char
charLexeme = lexeme . char

semicolon :: Parser ()
semicolon = label "semicolon" $ charLexeme ';' $> ()

boolP :: Parser Literal
boolP = label "bool" $ stringStandalone "true" $> BoolLit True <|> stringStandalone "false" $> BoolLit False

numP :: Parser Literal
numP = label "num" $ lexeme $ NumLit <$> try simpleFloat
    where
        signedNoSpace = L.signed (return ())
        -- float but no exponents
        simpleFloat   = signedNoSpace $ parseFloat <$> L.decimal <*> optional ((,) <$> char '.' <*> L.decimal)
        parseFloat w (Just (_, d)) = read (show w ++ ('.' : show d))
        parseFloat w Nothing       = fromIntegral w

strP :: Parser Literal
strP = label "string" $ lexeme $ fmap StrLit $ char '"' *> manyTill L.charLiteral (char '"')

nilP :: Parser Literal
nilP = label "nil" $ stringStandalone "nil" $> Nil

operators :: [[Operator Parser ExprO]]
operators =
    [ [Prefix (unaryChained '-' Neg), Prefix (unaryChained '!' Not)]
    , [InfixL (binary "or" Or), InfixL (binary "and" And)]
    , [InfixL (binary "*" Times), InfixL (binary "/" Div)]
    , [InfixL (binary "+" Plus), InfixL (binary "-" Minus)]
    , [InfixL (binary ">=" GtE), InfixL (binary ">" Gt), InfixL (binary "<=" LtE), InfixL (binary "<" Lt)]
    , [InfixL (binary "==" Eq), InfixL (binary "!=" NEq)]
    ]
    where
        toLocationInner = flip WithOffset <$> getOffset
        binary s t = (\o a b -> combineExprO (`BinOp` o) a b) <$> (toLocationInner <*> (symbol s $> t))
        -- combines expros with function, taking the earliest offset
        combineExprO f a@(WithOffset _ ao) b@(WithOffset _ bo) | ao < bo   = WithOffset (f a b) ao
                                                               | otherwise = WithOffset (f a b) bo
        unaryChained :: Char -> UnaryOp -> Parser (ExprO -> ExprO)
        unaryChained c t =
            foldr1 (.) <$> some (liftA2 (.) toLocationInner (UnOp <$> (toLocationInner <*> (char c $> t))))

identP :: Parser Identifier
identP = label "identifier" $ lexeme $ try $ ((:) <$> identStartP <*> many alphaNumChar) <* notFollowedBy alphaNumChar
    where
        identStartP :: Parser Char
        identStartP = letterChar <|> char '_'

assignmentP :: Parser Expr
assignmentP = label "assignment" $ try $ lexeme $ Assign <$> withLocation identP <* charLexeme '=' <*> exprP

-- TODO fail on 255 arg
callP :: Parser Expr
callP = toCall <$> exprP <*> between (charLexeme '(')
                                     (charLexeme ')')
                                     (optional ((:) <$> exprP <*> many (charLexeme ',' *> exprP)))
    where toCall e mas = Call e (fromMaybe [] mas)

exprP :: Parser ExprO
exprP = label "expression" $ makeExprParser
    (   between (charLexeme '(') (charLexeme ')') exprP
    <|> withLocation (callP <|> assignmentP <|> (Lit <$> (boolP <|> numP <|> strP <|> nilP)) <|> Ident <$> identP)
    )
    operators

blockP :: Parser [DeclO]
blockP = label "block" $ between (charLexeme '{') (charLexeme '}') (many declP)

ifP :: Parser Control
ifP =
    label "if statement"
        $   stringStandalone "if"
        *>  (If <$> between (charLexeme '(') (charLexeme ')') exprP)
        <*> stmtP
        <*> optional (stringStandalone "else" *> stmtP)

whileP :: Parser Control
whileP =
    label "while statement"
        $   stringStandalone "while"
        *>  (While <$> between (charLexeme '(') (charLexeme ')') exprP)
        <*> stmtP

-- returns a block
forP :: Parser Stmt
forP =
    label "for statement"
        $   (\o (s, mc, ma) rs -> toWhile o s mc ma rs)
        <$> getOffset
        <*> (stringStandalone "for" *> between
                (charLexeme '(')
                (charLexeme ')')
                (   (,,)
                <$> (fmap VarDecl <$> varP <|> fmap (StmtD . ExprStmt) <$> exprP)
                <*  semicolon
                <*> term
                <*  semicolon
                <*> term
                )
            )
        <*> stmtP
    where
        -- offset, beginning statement, maybe of condition, maybe of action, run statement
        toWhile o d mc ma s = Block
            [d, WithOffset (StmtD (Cont (While c (WithOffset (Block ((StmtD <$> s) : as)) (-1))))) o]            where
                c  = fromMaybe (Lit (BoolLit True)) <$> mc
                as = case ma of
                    WithOffset a o -> maybe [] ((: []) . (`WithOffset` o) . StmtD . ExprStmt) a
        term = withLocation $ optional (unOffset <$> exprP)

returnP :: Parser Stmt
returnP = label "return statement" $ ReturnStmt <$> (stringStandalone "return" *> exprP)

stmtP :: Parser StmtO
stmtP =
-- parens are technically unneccessary, but more readable (ish) and makes brittany format it reasonably
    withLocation
        $   returnP
        <|> (Cont <$> ifP)
        <|> (Cont <$> whileP)
        <|> forP
        <|> (Print <$> (stringStandalone "print" *> exprP) <* semicolon)
        <|> (Block <$> blockP)
        <|> (ExprStmt . unOffset <$> exprP <* semicolon)

stmtsP :: Parser [StmtO]
stmtsP = catMaybes <$> (many stmtWithRec <* eof)
    where stmtWithRec = withRecovery ((*> (Nothing <$ advUntilSemicolon)) . registerParseError) (Just <$> stmtP)

varP :: Parser VarDeclarationO
varP =
    withLocation
        $   lexeme
        $   stringStandalone "var"
        *>  ((\i v -> VarDeclaration i (fromMaybe (WithOffset (Lit Nil) (-1)) v)) <$> withLocation identP)
        <*> optional (charLexeme '=' *> exprP)

declP :: Parser DeclO
declP = withLocation $ VarDecl . unOffset <$> (varP <* semicolon) <|> StmtD . unOffset <$> stmtP

declsP :: Parser [DeclO]
declsP = catMaybes <$> (many declWithRec <* eof)
    where declWithRec = withRecovery ((*> (Nothing <$ advUntilSemicolon)) . registerParseError) (Just <$> declP)

advUntilSemicolon :: Parser ()
-- some instead of many to prevent infinite loop
advUntilSemicolon = void $ some (void strP <|> void (anySingleBut ';')) *> semicolon
