import Network
import Network.Socket
import States
import State.Var
import Interface.IO

-- Possible states of a random number server
data ServerState = Idle  -- not started yet
                 | Ready -- ready to accept incoming requests
                 | Waiting -- connected, ready to receive a request
                 | Processing -- received request, ready to send reply
                 | Done -- reply completed

-- Operations on a running server
data RandOp : SM_sig ServerState where
     -- Start and stop the server
     Start  : RandOp Bool Idle (\res => if res then Ready else Done)
     Quit  : RandOp () Ready (const Idle)

     -- Receive a request if the server is connected to a client
     RecvReq : RandOp (Maybe Integer) Waiting
                      (\res => case res of
                                    Nothing => Done
                                    Just _ => Processing)
     -- Send a reply if the server has received a request
     SendResp : Integer -> RandOp () Processing (const Done)
     -- Get the seed for the RNG, if the server is running
     GetSeed : RandOp Integer Ready (const Ready)

-- Operation which allows us to create a connection
data RandCreate : SM_sig ServerState where
     Accept : RandCreate Bool Ready (\res => if res then Waiting else Done)

-- We can close a server if it's Idle (i.e. not started) or Done (i.e.
-- responded to a request)
data RandFinal : ServerState -> Type where
     IdleFinal : RandFinal Idle
     DoneFinal : RandFinal Done

RandServer : SM ServerState
RandServer = MkSM Idle RandFinal RandOp RandCreate

-- A server loop keeps making connections to clients and running a session
-- which reads an input, and sends a reply
serverLoop : ConsoleIO io => 
             (s : State RandServer) -> 
             SMTrans io () [Stable s (RandServer, Ready)]
serverLoop s = do num <- on s GetSeed
                  (True, session) <- newFrom s Accept
                         | (False, session) => do delete session
                                                  serverLoop s
                  -- We now have the server 's' and a running session, 'session'
                  Just bound <- on session RecvReq
                       | Nothing => do delete session
                                       serverLoop s
                  on session (SendResp (num `mod` (bound + 1)))
                  -- Session is complete, we can delete it
                  delete session
                  serverLoop s

-- Start up a server, then run the server loop
startServer : ConsoleIO io => SMNew io () [RandServer]
startServer = do s <- new RandServer
                 True <- on s Start
                    | False => do putStrLn "Couldn't start server"
                                  delete s
                 call (serverLoop s)
                 on s Quit
                 delete s

-- Run the RandServer by using the Network sockets API, and a 'Var' to
-- hold the seed
ConsoleIO io => Transform RandServer [Net, Var] [Var] io where
    -- Translate random number server states to states in underlying SMs
    toState Idle = (Closed, ())
    toState Ready = (Listening, Integer) -- only have seed when running
    toState Waiting = (Open Server, ()) -- seed held in outer session
    toState Processing = (Open Server, ())
    toState Done = (Closed, ())

    -- Show that initial and final states are consistent
    initOK = Refl
    finalOK Idle IdleFinal = (ClosedFinal, ())
    finalOK Done DoneFinal = (ClosedFinal, ())

    -- Implement state transitions in terms of state transitions on Net/Var
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

    -- Create a new session by creating a new seed/connection
    createAs (server, seed) Accept 
         = do seed' <- new Var
              (Right addr, conn) <- newFrom server Accept
                   | (Left err, conn) => pure ((conn, seed'), False)
              pure ((conn, seed'), True)

main : IO ()
main = run (Main.startServer)
