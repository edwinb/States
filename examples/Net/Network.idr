module Network

import States
import Network.Socket
import Interface.IO

data Role = Client | Server

data SocketState = Closed
                 | Ready
                 | Bound Role
                 | Connected
                 | Listening
                 | Open Role

data NetOp : SM_sig SocketState where
     Socket : SocketType -> 
              NetOp (Either SocketError Socket) Closed
                    (either (const Closed) (const Ready))
     Bind : (addr : Maybe SocketAddress) -> (port : Port) ->
            NetOp (Either () ()) Ready 
                  (either (const Closed)
                          (const (case addr of
                                       Nothing => Bound Server
                                       Just _ => Bound Client)))
     Listen : NetOp (Either () ()) (Bound Server)
                    (\res => case res of
                                  Left err => Closed
                                  Right _ => Listening)
     Connect : SocketAddress -> Port ->
               NetOp (Either () ()) (Bound Client)
                     (either (const Closed) (const (Open Client)))
     Close : NetOp () st (\res => Closed)
     Send : String -> NetOp (Either () ()) (Open x) 
                            (either (const Closed) (const (Open x)))
     Recv : NetOp (Either () String) (Open x) 
                  (either (const Closed) (const (Open x)))

data NetCreate : SM_sig SocketState where
     Accept : NetCreate (Either SocketError SocketAddress) Listening
                        (either (const Closed) (const (Open Server)))

data NetFinal : SocketState -> Type where
     ClosedFinal : NetFinal Closed

Net : SM SocketState
Net = MkSM Closed NetFinal NetOp NetCreate

rndServer : ConsoleIO io =>
            (socket : State Net) ->
            Integer -> SMTrans io () [Trans socket (Net, Listening) (const Closed)]
rndServer socket seed = do
    (Right addr, conn) <- newFrom socket Accept
          | (Left addr, conn) => do delete conn; on socket Close

    Right msg <- on conn Recv
          | Left err => do delete conn; on socket Close
    printLn msg

    let bound = the Integer (cast msg)
    let seed' = (1664525 * seed + 1013904223) `prim__sremBigInt` (pow 2 32)

    Right ok <- on conn (Send (show (seed' `mod` (bound + 1))))
          | Left err => do delete conn; on socket Close

    on conn Close
    delete conn
    rndServer socket seed'

startServer : ConsoleIO io =>
              SMNew io () [Net]
startServer = do socket <- new Net
                 Right ok <- on socket (Socket Stream)
                       | Left err => do delete socket; pure ()
                 Right ok <- on socket (Bind Nothing 9442)
                       | Left err => do delete socket; pure ()
                 Right ok <- on socket Listen 
                       | Left err => do delete socket; pure ()
                 call (rndServer socket 123456789)
                 delete socket

ConsoleIO io => Execute Net io where
-- TODO

ConsoleIO io => Create Net io where

main : IO ()
main = run startServer


