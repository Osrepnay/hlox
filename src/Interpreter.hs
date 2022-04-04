module Interpreter where

import           Control.Applicative
import           Control.Monad.Trans.State.Strict
import           Data.Bifunctor
import           Data.Bool
import           Data.Functor
import           Data.List
import           Data.List.NonEmpty               (NonEmpty (..))
import qualified Data.List.NonEmpty               as NE
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as M
import           Data.Maybe
import           Data.Set                         (Set)
import qualified Data.Set                         as S
import           Data.Text                        (Text)
import qualified Data.Text                        as T
import           Data.Validation
import           Data.Void
import           Parser
import           Text.Megaparsec                  hiding (State)

data RuntimeError = WrongType Int String String | VarNotFound Int String | Return Int Value
runtimeToParseError :: RuntimeError -> ParseError Text Void
runtimeToParseError (WrongType o u e) =
    TrivialError o
    (Just $ Label $ NE.fromList u)
    (S.singleton $ Label $ NE.fromList e)
runtimeToParseError (VarNotFound o i) = FancyError o (S.singleton $ ErrorFail $ "variable " ++ i ++ " not found")
runtimeToParseError (Return      o _) = FancyError o (S.singleton $ ErrorFail "can't return here") -- when return isn't caught by call, meaning that it wasn't run in a function

-- head is inner scope, last is global
type RunState = NonEmpty (Map Identifier ValueO)

type ValueO = WithOffset Value
data Value = ParseVal Literal | BuiltinFunc (StateT RunState IO Value)

newState :: RunState
newState = M.empty :| []

addVar :: Identifier -> ValueO -> RunState -> RunState
addVar i l (e :| es) = M.insert i l e :| es

-- if not found, do nothing
modVar :: Identifier -> ValueO -> RunState -> RunState
modVar i l (e :| []             ) = bool e (M.insert i l e) (M.member i e) :| []
modVar i l (e :| res@(esh : est)) = bool (NE.cons e (modVar i l (esh :| est))) (M.insert i l e :| res) (M.member i e)

pushScope :: RunState -> RunState
pushScope = NE.cons M.empty

-- doesn't fail because every popScope is with a pushScope in a block
popScope :: RunState -> RunState
popScope = NE.fromList . NE.tail

stateLookup :: Identifier -> RunState -> Maybe ValueO
stateLookup i (e :| []         ) = M.lookup i e
stateLookup i (e :| (esh : est)) = M.lookup i e <<> stateLookup i (esh :| est)
  where
    Just a <<> _ = Just a
    _      <<> b = b

stateExists :: Identifier -> RunState -> Bool
stateExists i (e :| []         ) = M.member i e
stateExists i (e :| (esh : est)) = M.member i e || stateExists i (esh :| est)


runDecl :: DeclO -> StateT RunState IO [RuntimeError]
runDecl (WithOffset (StmtD s) o) = runStmt (WithOffset s o)
runDecl (WithOffset (VarDecl (VarDeclaration (WithOffset i _) e)) o) =
    runExpr e >>= validation pure (($> []) . modify . addVar i)

runDecls :: [DeclO] -> StateT RunState IO [RuntimeError]
runDecls []       = pure []
runDecls (d : ds) = runDecl d >>= (\es -> if null es then runDecls ds else pure es)

runStmt :: StmtO -> StateT RunState IO [RuntimeError]
runStmt (WithOffset (ExprStmt e) o) = validation id (const []) <$> runExpr (WithOffset e o)
runStmt (WithOffset (Print e) _) =
    mapStateT (>>= (\(v, s) -> flip (,) s <$> validation pure (($> []) . putStrLn) v))
        $ fmap (\(WithOffset x _) -> case x of
            ParseVal (StrLit  s) -> s
            ParseVal (BoolLit b) -> if b then "true" else "false"
            ParseVal (NumLit  n) -> let roundN = round n in if n == fromInteger roundN then show roundN else show n
            ParseVal Nil         -> "nil"
            ParseVal (Func    _) -> "function" -- TODO attach name to Func, and return placeholder if none
            BuiltinFunc _        -> "function")
        <$> runExpr e
runStmt    (WithOffset (Block ds) _) = modify pushScope *> runDecls ds <* modify popScope
runStmt st@(WithOffset (Cont  c ) _) = case c of
    If e es efm -> case efm of
        Just ef -> runExpr e >>= validation pure runStmt . fmap (bool ef es . unOffset) . (`bindValidation` castBool)
        Nothing ->
            runExpr e
                >>= validation pure id
                .   fmap (bool (pure []) (runStmt es) . unOffset)
                .   (`bindValidation` castBool)
    While e es -> while e es
      where
        while e es =
            runExpr e
            >>= validation pure id
            .   fmap (bool (pure []) (runStmt es *> while e es) . unOffset)
            .   (`bindValidation` castBool)
runStmt (WithOffset (ReturnStmt e) _) = validation id ((: []) . returnVal) <$> runExpr e
  where returnVal (WithOffset v o) = Return o v

runStmts :: [StmtO] -> StateT RunState IO [RuntimeError]
runStmts []       = pure []
runStmts (s : ss) = runStmt s >>= (\es -> if null es then runStmts ss else pure es)

-- filename, text, run, parser
-- uses parsing parser to format errors from interpreter
fmtErrorsP :: String -> Text -> (a -> StateT RunState IO [RuntimeError]) -> Parser a -> Parser (IO String)
fmtErrorsP f s r = fmap
    (fmap (maybe "" (errorBundlePretty . bundle) . NE.nonEmpty . fmap runtimeToParseError)
    . flip evalStateT newState
    . r)
      where
        bundle es = ParseErrorBundle
            { bundleErrors   = es
            , bundlePosState =
                PosState
                    { pstateInput      = s
                    , pstateOffset     = 0
                    , pstateSourcePos  = initialPos f
                    , pstateTabWidth   = defaultTabWidth
                    , pstateLinePrefix = ""
                    }
            }

-- <> except returns first value if second is fail
mergeValidation a b@(Success _) = a <> b
mergeValidation a b@(Failure _) = a

runExpr :: ExprO -> StateT RunState IO (Validation [RuntimeError] ValueO)
runExpr (WithOffset (Lit l                  ) o) = pure $ pure (WithOffset (ParseVal l) o)
runExpr (WithOffset (UnOp (WithOffset p o) v) _) = case p of
    Neg -> fmap (fmap (ParseVal . NumLit . negate)) . (`bindValidation` castNum) <$> runExpr v
    Not -> fmap (fmap (ParseVal . BoolLit . not)) . (`bindValidation` castBool) <$> runExpr v
runExpr (WithOffset (BinOp v0 (WithOffset p o) v1) _) = case p of
    Plus  -> runBin castNum (liftOffset2 (+) NumLit) </> runBin castStr (liftOffset2 (++) StrLit)
    Minus -> runBin castNum (liftOffset2 (-) NumLit)
    Times -> runBin castNum (liftOffset2 (*) NumLit)
    Div   -> runBin castNum (liftOffset2 (/) NumLit)
    Eq    -> runBin castBool (liftOffset2 (==) BoolLit)
        </> runBin castNum (liftOffset2 (==) BoolLit)
        </> runBin castStr (liftOffset2 (==) BoolLit)
    NEq -> runBin castBool (liftOffset2 (/=) BoolLit)
        </> runBin castNum (liftOffset2 (/=) BoolLit)
        </> runBin castStr (liftOffset2 (/=) BoolLit)
    Lt  -> runBin castNum (liftOffset2 (<) BoolLit)
    Gt  -> runBin castNum (liftOffset2 (>) BoolLit)
    LtE -> runBin castNum (liftOffset2 (<=) BoolLit)
    GtE -> runBin castNum (liftOffset2 (>=) BoolLit)
    Or  -> runBin castBool (liftOffset2 (||) BoolLit)
    And -> runBin castBool (liftOffset2 (&&) BoolLit)
  where
    a </> b = mergeValidation <$> a <*> b
    runBin cf f = liftA2 f . bindCf <$> runExpr v0 <*> (bindCf <$> runExpr v1)
      where bindCf = (`bindValidation` cf)
    liftOffset2 f c (WithOffset n0 o) (WithOffset n1 _) = WithOffset (ParseVal $ c $ f n0 n1) o
runExpr (WithOffset (Ident i) o) = validationFromMaybe [VarNotFound o i] . stateLookup i <$> get
  where
    validationFromMaybe _ (Just x) = Success x
    validationFromMaybe f Nothing  = Failure f
runExpr (WithOffset (Assign (WithOffset i o) e) _) =
    get
        >>= fmap joinValidation
        .   sequenceA
        .   ($> (runExpr e >>= traverse (\l -> l <$ modify (modVar i l))))
        .   bool (Failure [VarNotFound o i]) (Success ())
        .   stateExists i
  where
    joinValidation (Failure f) = Failure f
    joinValidation (Success s) = s
runExpr (WithOffset (Call f as) o) = do
    l <- runExpr f
    let fn = l `bindValidation` castFunc
    -- run fn lines
    let fnR =
            fmap
                (fmap (\es -> case es of
                     Return _ x : _ -> Success x
                     es             -> Failure es)
                .   runDecls)
            <$> fn
    -- collapse surrounding Validation
    let fnS = case fnR of
            Success (WithOffset s vo) -> fmap (`WithOffset` vo) <$> s
            Failure es                -> pure (Failure es)
    let bFn = l `bindValidation` castFuncBuiltin
    let bFnS = case bFn of
                Success (WithOffset s vo) -> Success . (`WithOffset` vo) <$> s
                Failure es                -> pure (Failure es)
    mergeValidation <$> fnS <*> bFnS

showValueType :: Value -> String
showValueType v = case v of
    ParseVal l -> case l of
        BoolLit _ -> "bool"
        NumLit  _ -> "num"
        StrLit  _ -> "string"
        Func    _ -> "function"
        Nil       -> "nil"
    BuiltinFunc _ -> "function"

castBool :: ValueO -> Validation [RuntimeError] (WithOffset Bool)
castBool (WithOffset l o) = Success $ flip WithOffset o $ case l of
    ParseVal (BoolLit x) -> x
    ParseVal Nil         -> False
    _                    -> True

castNum :: ValueO -> Validation [RuntimeError] (WithOffset Double)
castNum (WithOffset l o) = case l of
    ParseVal (NumLit x) -> Success (WithOffset x o)
    v                   -> Failure [WrongType o (showValueType v) "num"]

castStr :: ValueO -> Validation [RuntimeError] (WithOffset String)
castStr (WithOffset l o) = case l of
    ParseVal (StrLit x) -> Success (WithOffset x o)
    v                   -> Failure [WrongType o (showValueType v) "string"]

castFunc :: ValueO -> Validation [RuntimeError] (WithOffset [DeclO])
castFunc (WithOffset l o) = case l of
    ParseVal (Func x) -> Success (WithOffset x o)
    v                 -> Failure [WrongType o (showValueType v) "function"]

castFuncBuiltin :: ValueO -> Validation [RuntimeError] (WithOffset (StateT RunState IO Value))
castFuncBuiltin (WithOffset l o) = case l of
    BuiltinFunc x -> Success (WithOffset x o)
    v             -> Failure [WrongType o (showValueType v) "function"]
