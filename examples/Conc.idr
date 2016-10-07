import States

import System.Concurrency.Channels
import Interface.IO

data ServerState
        = None -- Initial state
        | Waiting (request -> Type) -- Final state (so can't listen and not reply)
        | Processing (request -> Type) Type 

data ServerFinal : ServerState -> Type where
     WaitingIsFinal : ServerFinal (Waiting iface)
     NoneIsFinal : ServerFinal None

data Process : (request -> Type) -> Type where
     MkProcess : PID -> Process iface

data ServerOp : SM_sig ServerState where
     Fork : (iface : request -> Type) ->
            ServerOp (Maybe (Process iface)) None 
                     (\res => case res of
                                   Nothing => Waiting iface
                                   Just pid => None)
     Listen : {iface : request -> Type} ->
              (timeout: Int) ->
              ServerOp (Maybe request)
                       (Waiting iface)
                            (\res => case res of
                                          Nothing => Waiting iface
                                          Just msg => Processing iface (iface msg))
     Reply : {iface : request -> Type} ->
             (reply : responsetype) ->
             ServerOp () (Processing iface responseType) 
                         (const (Waiting iface))

Server : SM ServerState
Server = MkSM None ServerFinal ServerOp

Execute Server IO where
    resource None = ()
    resource (Waiting f) = ()
    resource (Processing f x) = Channel

    initialise = ()

    exec res (Fork iface) k 
        = do pid <- spawn (do k Nothing res
                              pure ())
             k (Just (MkProcess pid)) ()
    exec res (Listen {request} timeout) k 
        = do Just chan <- listen timeout
                  | Nothing => k Nothing res
             Just req <- unsafeRecv request chan
                  | Nothing => k Nothing res
             k (Just req) chan
    exec res (Reply reply) k 
        = do unsafeSend res reply
             k () ()


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
              (s : State Server) ->
              SMTrans m () [Stable s Server (Waiting ArithResponse)]
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
              SMNew m () [Client, Server]
arithClient = with States do 
                 server <- new Server
                 Just proc <- on server (Fork ArithResponse)
                      | Nothing => do call (arithServer server)
                                      delete server
                 delete server -- Not needed any more
                 chan <- new Client
                 putStr "Number: "
                 num <- getStr
                 True <- on chan (Connect proc)
                            | False => do putStrLn "Server died"
                                          delete chan
                 on chan (Send (Add (cast num) 94))
                 answer <- on chan Receive
                 putStrLn (num ++ " + 94 = " ++ show answer)
                 
                 True <- on chan (Connect proc)
                            | False => do putStrLn "Server died"
                                          delete chan
                 on chan (Send (Negate (cast num)))
                 answer <- on chan Receive
                 putStrLn ("-" ++ num ++ " = " ++ show answer)

                 delete chan

main : IO ()
main = run arithClient

