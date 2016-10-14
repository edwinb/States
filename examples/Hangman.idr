import Data.Vect

import States
import State.Var
import Interface.IO

{- We'll need this later... -}
total
removeElem : (value : a) -> (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = There later}
                                          = y :: removeElem value ys

{- Global states of a hangman game -}
data HangmanState = Unstarted | Playing | Won | Lost

{- The game is over if it's either won or lost -}
data GameEnd : HangmanState -> Type where
     GameWon : GameEnd Won
     GameLost : GameEnd Lost

{- We can create a new game with a target word, and play the game -}
data HangmanOp : SM_sig HangmanState where
     NewGame : (word : String) -> HangmanOp () Unstarted (const Playing)
     Play : HangmanOp Bool Playing (\res => case res of
                                                 True => Won
                                                 False => Lost)

data HangmanData : HangmanState -> Type where
     Word : String -> HangmanData Playing
     NoWord : HangmanData x

Hangman : SM HangmanState
Hangman = MkSM Unstarted -- Initial state
               GameEnd -- Predicate for final states
               HangmanOp -- Operations on the state machine
               None -- No creation

{- Top level game, creates a new game then plays it -}
hangman : ConsoleIO io => SMNew io () [Hangman]
hangman = do game <- new Hangman
             on game $ NewGame "testing"
             result <- on game Play
             case result of
                  False => do putStrLn "You lose"
                              delete game
                  True => do putStrLn "You win"
                             delete game


{- To implement the game, we'll define another state machine which
   describes the rules of the game -}
data GameState = Score Nat Nat -- Number of guesses left; number of letters to guess
               | NotRunning

data Finished : GameState -> Type where
     GameFinished : Finished NotRunning

letters : String -> List Char
letters str = map toUpper (nub (unpack str))

data GameOp : SM_sig GameState where
     {- We can guess a character if there are still both guesses remaining
        and letters to guess. The result determines whether we lose a guess,
        or lose a letter -}
     Guess : Char -> GameOp Bool (Score (S g) (S l))
                            (\res => case res of
                                          False => Score g (S l)
                                          True => Score (S g) l)
     {- Read a guess from the player -}
     ReadGuess : GameOp Char (Score (S g) (S l)) (const (Score (S g) (S l)))

     {- We can claim a win if there are no letters to guess -}
     ClaimWin  : GameOp () (Score (S g) 0) (const NotRunning)
     {- We can admit defeat if there are no guesses left -}
     AdmitLoss : GameOp () (Score 0 (S l)) (const NotRunning)

     {- Get a string representation of the current game state -}
     GetState  : GameOp String st (const st)

     {- Start a new game with a target word -}
     SetTarget : (word : String) -> GameOp () NotRunning 
                                      (const (Score 6 (length (letters word))))


Game : SM GameState
Game = MkSM NotRunning Finished GameOp None


{- Implementation of the game rules, starts with a number of guesses and
   letters to guess, can only end either in victory or defeat (NotRunning) -}
play : ConsoleIO io =>
       (game : State Game) ->
       SMTrans io Bool [Trans game (Game, Score (S g) l) (const NotRunning)]
play {g} {l = Z} game = do on game ClaimWin
                           pure True
play {g} {l = S l} game 
      = do st <- on game GetState
           putStrLn st
           letter <- on game ReadGuess
           ok <- on game (Guess letter)
           case ok of
                False => do putStrLn "Incorrect"
                            case g of
                                 Z => do on game AdmitLoss
                                         pure False
                                 S k => play game
                True => do putStrLn "Correct!"
                           play game

{- Now to define how the 'Hangman' and 'Game' state machines actually run -}

{- Run time representation of the game data -}
data GameData : GameState -> Type where
     InProgress : (target : String) -> (g : Nat) ->
                  (missing : Vect l Char) -> 
                  GameData (Score g l)
     MkNotRunning : (won : Bool) -> GameData NotRunning

Show (GameData g) where
    show (MkNotRunning won) = if won then "Game won" else "Game lost"
    show (InProgress word guesses missing) 
         = "\n" ++ pack (map hideMissing (unpack word)) 
               ++ "\n" ++ show guesses ++ " guesses left"
      where hideMissing : Char -> Char
            hideMissing c = if c `elem` missing then '-' else c 

{- Execute 'Game' in IO using 'GameData' -}
Execute Game IO where
    resource = GameData
    initialise = MkNotRunning False
    create res op k = pass op

    exec (InProgress word _ missing) (Guess x) k = 
         case isElem x missing of
              Yes prf => k True (InProgress word _ (removeElem x missing))
              No contra => k False (InProgress word _ missing)
    exec res ReadGuess k = do putStr "Guess: "
                              x <- getLine
                              case unpack (toUpper x) of
                                   [letter] => if isAlpha letter
                                                  then k letter res
                                                  else k ' ' res
                                   _ => k ' ' res
    exec res ClaimWin k = k () (MkNotRunning True)
    exec res AdmitLoss k = k () (MkNotRunning False)
    exec res GetState k = k (show res) res
    exec res (SetTarget word) k = k () (InProgress word _ (fromList (letters word)))

{- Implement 'Hangman' by translating it to a lower level state machine
   'Var', for storing the word. We can create a 'Game' state machine in 
   the process. -}
ConsoleIO m => Transform Hangman [Var] [Game] m where
    toState Unstarted = () -- No word stored
    toState Playing = String  -- Word stored
    toState Won = String
    toState Lost = String

    initOK = Refl -- Initial states 'Unstarted' and '()' correspond
    finalOK Won GameWon = ()
    finalOK Lost GameLost = ()


    {- Implement 'Hangman' ops using 'Var' to store the word. 
       We're also allowed to create 'Game' state machines as required, as it
       says in the implementation header. -}
    execAs word (NewGame x) = on word (Put x)
    execAs word Play = do x <- on word Get
                          game <- new Game
                          on game (SetTarget (toUpper x))
                          result <- call (play game)
                          delete game
                          case result of
                               True => pure True
                               False => pure False

    createAs word op = pass op

{- And then run it... -}
main : IO ()
main = run hangman
