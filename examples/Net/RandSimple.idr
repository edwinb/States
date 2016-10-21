import States
import State.Var
import Network
import Network.Socket
import Interface.IO

-- A simple server which reads an integer 'bound' and sends back a random
-- number between 0 and bound
rndServer : ConsoleIO io =>
            (socket : State Net) ->
            (seed : State Var) -> 
            SMs io () [] [Trans socket Listening (const Closed),
                          Stable seed Integer]
rndServer socket seed = do
    (Right addr, conn) <- newFrom socket Accept
          | (Left addr, conn) => do delete conn; on socket Close

    Right msg <- on conn Recv
          | Left err => do delete conn; on socket Close
    printLn msg

    let bound = the Integer (cast msg)
    val <- on seed Get
    let val' = (1664525 * val + 1013904223) `prim__sremBigInt` (pow 2 32)
    on seed (Put val')

    Right ok <- on conn (Send (show (val `mod` (bound + 1))))
          | Left err => do delete conn; on socket Close

    on conn Close
    delete conn
    rndServer socket seed

startServer : ConsoleIO io => SMs io () [Net, Var] []
startServer = do 
    socket <- new Net
    seed <- new Var
    on seed (Put 123456789)
    Right ok <- on socket (Socket Stream)
          | Left err => do delete socket; delete seed
    Right ok <- on socket (Bind Nothing 9442)
          | Left err => do delete socket; delete seed
    Right ok <- on socket Listen 
          | Left err => do delete socket; delete seed
    call (rndServer socket seed)
    delete socket
    delete seed

main : IO ()
main = run startServer
