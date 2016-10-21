module Network

import States
import Network.Socket

%access public export

data Role = Client | Server

data SocketState = Closed
                 | Ready
                 | Bound 
                 | Listening
                 | Open Role

data CloseOK : SocketState -> Type where
     CloseOpen : CloseOK (Open role)
     CloseListening : CloseOK Listening

-- Operations which change a socket state.
-- Use 'Either' for all the return types, for consistency (I may add
-- descriptive error types later)

data NetOp : SM_sig SocketState where
     Socket : SocketType -> 
              NetOp (Either SocketError ()) Closed
                    (either (const Closed) (const Ready))
     Bind : (addr : Maybe SocketAddress) -> (port : Port) ->
            NetOp (Either () ()) Ready 
                  (either (const Closed) (const Bound))
     Listen : NetOp (Either () ()) Bound
                  (either (const Closed) (const Listening))
     Connect : SocketAddress -> Port ->
               NetOp (Either () ()) Ready
                     (either (const Closed) (const (Open Client)))
     Close : {auto prf : CloseOK st} -> NetOp () st (\res => Closed)
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


-- How to run socket operations under 'IO'
Execute Net IO where
    resource Closed = ()
    resource Ready = Socket
    resource Bound = Socket
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
    exec res (Close {prf = CloseOpen}) k = do close res; k () ()
    exec res (Close {prf = CloseListening}) k = do close res; k () ()

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


