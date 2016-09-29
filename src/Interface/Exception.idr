module Interface.Exception

import States
import Control.IOExcept

%default total

public export
interface Exception (err : Type) (m : Type -> Type) where
  throw : err -> SMOp m ()

export
Exception err (IOExcept err) where
    throw e = lift (ioe_fail e)

Exception err Maybe where
    throw e = lift Nothing

Exception err (Either err) where
    throw e = lift (Left e)
