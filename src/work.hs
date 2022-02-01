
import Data.Word (Word8)
import qualified Control.Applicative as App

type Byte = Word8

data Token =
      Let
    | In
    | Sym Char
    | Var String
    | Int Int
    | EOF
    deriving (Eq, Show)

data AlexPosn = AlexPn !Int !Int !Int deriving (Eq,Show)

data AlexState = AlexState {
        alex_pos :: !AlexPosn,  -- position at current input location
        alex_inp :: String,     -- the current input
        alex_chr :: !Char,      -- the character before the input
        alex_bytes :: [Byte],
        alex_scd :: !Int        -- the current startcode
    }

newtype Alex a = Alex { unAlex :: AlexState -> Either String (AlexState, a) }

instance Functor Alex where
  fmap f a = Alex $ \s -> case unAlex a s of
                            Left msg -> Left msg
                            Right (s', a') -> Right (s', f a')

instance Applicative Alex where
  pure a   = Alex $ \s -> Right (s, a)
  fa <*> a = Alex $ \s -> case unAlex fa s of
                            Left msg -> Left msg
                            Right (s', f) -> case unAlex a s' of
                                               Left msg -> Left msg
                                               Right (s'', b) -> Right (s'', f b)

instance Monad Alex where
  m >>= k  = Alex $ \s -> case unAlex m s of
                                Left msg -> Left msg
                                Right (s',a) -> unAlex (k a) s'
  return = App.pure

newtype AlexPlus a = AlexPlus { unAlexPlus :: AlexState -> Either AlexState (AlexState, a) }

instance Functor AlexPlus where
  fmap f a = AlexPlus $ \s -> case unAlexPlus a s of
                                Left err -> Left err
                                Right (s', a') -> Right (s', f a')

instance Applicative AlexPlus where
  pure a   = AlexPlus $ \s -> Right (s, a)
  fa <*> a = AlexPlus $ \s -> case unAlexPlus fa s of
                                Left err -> Left err
                                Right (s', f) -> case unAlexPlus a s' of
                                                   Left err -> Left err
                                                   Right (s'', b) -> Right (s'', f b)

instance Monad AlexPlus where
  m >>= k  = AlexPlus $ \s -> case unAlexPlus m s of
                                Left err -> Left err
                                Right (s',a) -> unAlexPlus (k a) s'
  return = App.pure

fromAlex :: Alex a -> AlexPlus a
fromAlex a =
    AlexPlus $ \s -> case unAlex a s of
                       Left _ -> Left s
                       Right (s',a) -> Right (s', a)

alexStartPos :: AlexPosn
alexStartPos = AlexPn 0 1 1

runAlexPlus :: String -> AlexPlus a -> Either String a
runAlexPlus input__ (AlexPlus f)
   = case f (AlexState {alex_bytes = [],
                        alex_pos = alexStartPos,
                        alex_inp = input__,
                        alex_chr = '\n',
                        alex_scd = 0}) of Left err -> Left $ getErrorMsg err
                                          Right ( _, a ) -> Right a
    where
        getErrorMsg (AlexState _ s _ _ _,, err) err) =
            unlines [err, "Parse error on input '" ++ (head . words $ s) ++ "'", head $ lines s ]

alexMonadScan :: Alex Token
alexMonadScan = undefined

getAllResults :: AlexPlus [Token]
getAllResults = do
    x <- fromAlex alexMonadScan
    case x of
        EOF -> return [x]
        _ -> do
            xs <- getAllResults
            return $ x:xs

main = do
    s <- getContents
    putStrLn s
    print (runAlexPlus s getAllResults)
