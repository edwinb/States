import Network
import Network.Socket
import States
import State.Var
import Interface.IO

-- data SessionState : Type where
--      SendMsg : (msgType : Type) -> (msgType -> SessionState) -> SessionState
--      RecvMsg : (msgType : Type) -> (msgType -> SessionState) -> SessionState
--      Done : SessionState

data ServerState = Idle | Ready | Waiting | Processing | Done

data RandOp : SM_sig ServerState where
     Quit  : RandOp () Ready (const Idle)
     Start  : RandOp Bool Idle (\res => if res then Ready else Done)

     RecvReq : RandOp (Maybe Integer) Waiting
                      (\res => case res of
                                    Nothing => Done
                                    Just _ => Processing)
     SendResp : Integer -> RandOp () Processing (const Done)
     GetSeed : RandOp Integer Ready (const Ready)

data RandCreate : SM_sig ServerState where
     Accept : RandCreate Bool Ready (\res => if res then Waiting else Done)

data RandFinal : ServerState -> Type where
     IdleFinal : RandFinal Idle
     DoneFinal : RandFinal Done

RandServer : SM ServerState
RandServer = MkSM Idle RandFinal RandOp RandCreate

serverLoop : ConsoleIO io => 
             (s : State RandServer) -> 
             SMTrans io () [Stable s (RandServer, Ready)]
serverLoop s = do num <- on s GetSeed
                  (True, session) <- newFrom s Accept
                         | (False, session) => do delete session
                                                  serverLoop s
                  Just bound <- on session RecvReq
                       | Nothing => do delete session
                                       serverLoop s
                  on session (SendResp (num `mod` (bound + 1)))
                  delete session
                  serverLoop s

startServer : ConsoleIO io => SMNew io () [RandServer]
startServer = do s <- new RandServer
                 True <- on s Start
                    | False => do putStrLn "Couldn't start server"
                                  delete s
                 call (serverLoop s)
                 on s Quit
                 delete s

ConsoleIO io => Transform RandServer [Net, Var] [Var] io where
    toState Idle = (Closed, ())
    toState Ready = (Listening, Integer)
    toState Waiting = (Open Server, ()) -- seed held in outer session
    toState Processing = (Open Server, ())
    toState Done = (Closed, ())

    initOK = Refl
    finalOK Idle IdleFinal = (ClosedFinal, ())
    finalOK Done DoneFinal = (ClosedFinal, ())

    execAs (server, seed) Quit = do on server Close
                                    on seed (Put ())
    execAs (server, seed) Start 
         = do putStrLn "Starting server"
              Right ok <- on server (Socket Stream)
                    | Left err => pure False
              Right ok <- on server (Bind Nothing 9442)
                    | Left err => pure False
              Right ok <- on server Listen
                    | Left err => pure False
              on seed (Put 123456789)
              pure True
    execAs (server, seed) RecvReq 
         = do putStrLn "Received request"
              Right msg <- on server Recv
                    | Left err => pure Nothing
              pure (Just (cast msg))
    execAs (server, seed) (SendResp resp) 
         = do on server (Send (show resp))
              on server Close
              on seed (Put ())
    execAs (server, seed) GetSeed 
         = do sval <- on seed Get
              on seed (Put ((1664525 * sval + 1013904223) 
                           `prim__sremBigInt` (pow 2 32)))
              pure sval

    createAs (server, seed) Accept 
         = do seed' <- new Var
              (Right addr, conn) <- newFrom server Accept
                   | (Left err, conn) => pure ((conn, seed'), False)
              pure ((conn, seed'), True)

main : IO ()
main = run (Main.startServer)
