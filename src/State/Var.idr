module State.Var

import States

{- Read and write mutable values -}
public export
data VarOp : SM_sig Type where
     Get : VarOp a a (const a)
     Put : b -> VarOp () a (const b)

-- Mutable value state machine
public export
Var : SM Type
Var = MkSM () -- Initial state
           (\x => ()) -- All states are valid final states
           VarOp -- Operations on the state machine
           None -- No creators

export
Execute Var m where
    resource x = x
    initialise = () -- No value stored on initialisation

    exec res Get     k = k res res
    exec res (Put x) k = k () x

