module Network

import States
import Network.Socket
import Interface.IO

%access public export

data Role = Client | Server

data SocketState = Closed
                 | Ready
                 | Bound Role
                 | Connected
                 | Listening
                 | Open Role

-- Operations which change a socket state.
-- Use 'Either' for all the return types, for consistency (I may add
-- descriptive error types later)

data NetOp : SM_sig SocketState where
     Socket : SocketType -> 
              NetOp (Either SocketError ()) Closed
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
     Close : NetOp () st (\res => Closed) -- TODO: Only 'Open' and 'Listening'
     Send : String -> NetOp (Either () ()) (Open x) 
                            (either (const Closed) (const (Open x)))
     Recv : NetOp (Either () String) (Open x) 
                  (either (const Closed) (const (Open x)))

-- Operations which make a new socket from an existing socket
data NetCreate : SM_sig SocketState where
     Accept : NetCreate (Either SocketError SocketAddress) Listening
                        (either (const Closed) (const (Open Server)))

-- Socket states where we can delete the socket (just 'Closed')
data NetFinal : SocketState -> Type where
     ClosedFinal : NetFinal Closed

Net : SM SocketState
Net = MkSM Closed NetFinal NetOp NetCreate

{-
-- A simple server which reads an integer 'bound' and sends back a random
-- number between 0 and bound
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
                       | Left err => do delete socket
                 Right ok <- on socket (Bind Nothing 9442)
                       | Left err => do delete socket
                 Right ok <- on socket Listen 
                       | Left err => do delete socket
                 call (rndServer socket 123456789)
                 delete socket
                 -}

-- How to run socket operations under 'IO'
Execute Net IO where
    resource Closed = ()
    resource Ready = Socket
    resource (Bound x) = Socket
    resource Connected = Socket
    resource Listening = Socket
    resource (Open x) = Socket

    initialise = ()

    exec res (Socket ty) k = do Right sock <- socket AF_INET ty 0
                                      | Left err => k (Left err) ()
                                k (Right ()) sock

    exec res (Bind addr port) k = do ok <- bind res addr port
                                     if ok /= 0 
                                        then k (Left ()) () 
                                        else k (Right ()) (case addr of
                                                             Nothing => res
                                                             Just _ => res)
    exec res Listen k = do ok <- listen res
                           if ok /= 0
                              then k (Left ()) ()
                              else k (Right ()) res
    exec res (Connect addr port) k = do ok <- connect res addr port
                                        if ok /= 0
                                           then k (Left ()) ()
                                           else k (Right ()) res
    -- Only needs closing if it's actually open!
    -- (TODO: Really need the proof on 'Close')
    exec {in_state = Listening} res Close k = do close res
                                                 k () ()
    exec {in_state = (Open x)} res Close k = do close res
                                                k () ()
    exec res Close k = k () ()

    exec res (Send msg) k = do Right _ <- send res msg
                                    | Left _ => k (Left ()) ()
                               k (Right ()) res
    exec res Recv k = do Right (msg, len) <- recv res 1024 -- TMP HACK. I know :)
                             | Left _ => k (Left ()) ()
                         k (Right msg) res

-- How to run socket creation operations under 'IO'
    create res Accept k = do Right (conn, addr) <- accept res
                                   | Left err => k (Left err) ()
                             k (Right addr) conn

-- main : IO ()
-- main = run startServer


