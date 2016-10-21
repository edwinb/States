import States
import Network
import Network.Socket
import Interface.IO

client_main : ConsoleIO io =>
              (socket : State Net) -> SMs io () [] [Stable socket Closed]
client_main socket
  = do putStr "Bound: "
       x <- getStr
       Right ok <- on socket (Socket Stream)
          | Left err => putStrLn "Error on socket creation"
       Right ok <- on socket (Connect (Hostname "localhost") 9442)
          | Left err => putStrLn "Error on connect"
       Right ok <- on socket (Send x)
          | Left err => putStrLn "Send failed"
       Right reply <- on socket Recv
          | Left err => putStrLn "Error on recv"
       putStrLn reply
       on socket Close

client_start : ConsoleIO io => SMs io () [Net] []
client_start = do socket <- new Net
                  call (client_main socket)
                  delete socket

main : IO ()
main = run client_start
