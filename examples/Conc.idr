import States

import System.Concurrency.Channels
import Interface.IO
import State.Var

data ConcState
        = None -- Initial/Final state
        | Waiting (request -> Type) -- Final state (so can't listen and not reply)
        | Processing (request -> Type) Type 
        | Finished

data ConcFinal : ConcState -> Type where
     WaitingIsFinal : ConcFinal (Waiting iface)
     NoneIsFinal : ConcFinal None
     FinishedIsFinal : ConcFinal Finished

data Process : (request -> Type) -> Type where
     MkProcess : PID -> Process iface

data ForkThread : (request -> Type) -> Type where
     Main : (Process iface) -> ForkThread iface
     Child : ForkThread iface

data ConcOp : SM_sig ConcState where
     Fork : (iface : request -> Type) ->
            ConcOp (ForkThread iface) None 
                   (\server => case server of
                                    Main iface => None
                                    Child => Waiting iface)
     Listen : {iface : request -> Type} ->
              (timeout: Int) ->
              ConcOp (Maybe request)
                       (Waiting iface)
                            (\res => case res of
                                          Nothing => Waiting iface
                                          Just msg => Processing iface (iface msg))
     Reply : {iface : request -> Type} ->
             (reply : responsetype) ->
             ConcOp () (Processing iface responseType) 
                         (const (Waiting iface))
     QuitThread : ConcOp any (Waiting iface) (const Finished)

Conc : SM ConcState
Conc = MkSM None ConcFinal ConcOp

-- TODO: Change the types so that a server *must* run indefinitely and so
-- we know we'll get a reply
-- Also add loop to States so that we can have total programs that run forever
fork : ((s : State Conc) -> 
             SMTransNew m () ops [Stable s (Conc, Waiting iface)]) -> 
       SMNew m (Process iface) (Conc :: ops)
fork {iface} server
     = do s <- new Conc
          Main pid <- on s (Fork iface)
               | Child => do call (server s)
                             ret <- on s QuitThread
                             delete s
                             pure ret
          delete s
          pure pid

Execute Conc IO where
    resource None = ()
    resource (Waiting f) = ()
    resource (Processing f x) = Channel
    resource Finished = ()

    initialise = ()

    exec res (Fork iface) k 
        = do pid <- spawn (do k Child res
                              pure ())
             k (Main (MkProcess pid)) ()
    exec res (Listen {request} timeout) k 
        = do Just chan <- listen timeout
                  | Nothing => k Nothing res
             Just req <- unsafeRecv request chan
                  | Nothing => k Nothing res
             k (Just req) chan
    exec res (Reply reply) k 
        = do unsafeSend res reply
             k () ()
    exec res QuitThread k = stopThread

data ClientState 
        = Disconnected -- Initial and final state
        | SendReady (request -> Type)
        | ReceiveReady (request -> Type) Type

data ClientFinal : ClientState -> Type where
     DisconnectedIsFinal : ClientFinal Disconnected

data ClientOp : SM_sig ClientState where
     Connect : {iface : request -> Type} ->
               Process iface ->
               ClientOp Bool Disconnected
                        (\res => case res of
                                      False => Disconnected
                                      True => SendReady iface)
     Send : {iface : request -> Type} ->
            (msg : request) -> 
            ClientOp () (SendReady iface)
                        (const (ReceiveReady iface (iface msg)))
     Receive : {iface : request -> Type} ->
               ClientOp t (ReceiveReady iface t)
                          (const Disconnected)

Client : SM ClientState
Client = MkSM Disconnected ClientFinal ClientOp

request : {iface : request -> Type} ->
          (chan : State Client) -> (process : Process iface) ->
          (req : request) -> 
          SMTrans m (Maybe (iface req)) [Stable chan (Client, Disconnected)]
request chan proc req = do True <- on chan (Connect proc)
                             | False => pure Nothing
                           on chan (Send req)
                           answer <- on chan Receive
                           pure (Just answer)


Execute Client IO where
    resource Disconnected = ()
    resource (SendReady f) = Channel
    resource (ReceiveReady f x) = Channel

    initialise = ()

    exec res (Connect (MkProcess pid)) k 
          = do Just chan <- connect pid
                    | Nothing => k False ()
               k True chan
    exec res (Send msg) k
          = do unsafeSend res msg
               k () res
    exec res (Receive {t}) k 
          = do Just res <- unsafeRecv t res
                    | Nothing => believe_me () -- Can't Happen...
               k res ()

data Arith = Add Nat Nat | Negate Int

ArithResponse : Arith -> Type
ArithResponse (Add k j) = Nat
ArithResponse (Negate k) = Int

covering
arithServer : ConsoleIO m => 
              (s : State Conc) ->
              SMTrans m () [Stable s (Conc, Waiting ArithResponse)]
arithServer s = do putStrLn "Waiting for message"
                   msg <- on s (Listen 2)
                   case msg of
                        Nothing => arithServer s
                        (Just (Add k j)) => do on s (Reply (k + j))
                                               arithServer s
                        (Just (Negate k)) => do on s (Reply (-k))
                                                arithServer s

covering
arithClient : ConsoleIO m =>
              SMNew m () [Client, Conc]
arithClient = do 
                 proc <- call (fork arithServer)
                 chan <- new Client
                 putStr "Number: "
                 num <- getStr

                 Just answer <- call $ request chan proc (Add (cast num) 94)
                       | Nothing => do putStrLn "Server died"
                                       delete chan
                 putStrLn (num ++ " + 94 = " ++ show answer)

                 Just answer <- call $ request chan proc (Negate (cast num))
                       | Nothing => do putStrLn "Server died"
                                       delete chan
                 putStrLn ("-" ++ num ++ " = " ++ show answer)
                 delete chan

main : IO ()
main = run arithClient
