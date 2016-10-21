import Network.Socket

acceptLoop : Integer -> Socket -> IO ()
acceptLoop seed sock 
    = do Right (conn, addr) <- accept sock
               | Left err => putStrLn "Accept fail"
         Right (msg, len) <- recv conn 80
         
         let num = the Integer (cast msg)
         let seed' = (1664525 * seed + 1013904223) `prim__sremBigInt` (pow 2 32)

         printLn msg
         send conn (show (seed' `mod` (num + 1)))

         close conn
         acceptLoop seed' sock

rnd_server : Integer -> IO ()
rnd_server seed =
  do Right sock <- socket AF_INET Stream 0
           | Left err => putStrLn "Socket fail"
     ok <- bind sock Nothing 9442 -- Socket not bound
     if (ok /= 0) then putStrLn "Bind fail"
        else 
          do ok <- listen sock -- Socket must be bound
             if (ok /= 0) then putStrLn "Listen fail"
                          else acceptLoop seed sock

main : IO ()
main = do putStrLn "Running on 9442"
          rnd_server 1234
