import States
import State.Var

data TwoVarOp : SM_sig (Type, Type) where
     GetA : TwoVarOp a (a, b) (const (a, b))
     GetB : TwoVarOp b (a, b) (const (a, b))

     SetA : c -> TwoVarOp () (a, b) (const (c, b))
     SetB : c -> TwoVarOp () (a, b) (const (a, c))

TwoVar : SM (Type, Type)
TwoVar = MkSM ((), ()) (\v => ()) TwoVarOp None

Transform TwoVar [Var, Var] [] m where
    toState (a, b) = (a, b)
    initOK = Refl
    finalOK (a, b) () = ((), ())

    execAs (vara, varb) GetA 
         = on vara Get
    execAs (vara, varb) GetB 
         = on varb Get
    execAs (vara, varb) (SetA x) 
         = on vara (Put x)
    execAs (vara, varb) (SetB x) 
         = on varb (Put x)

    createAs p op = pass op

test : SMNew m (Int, Int) [TwoVar]
test = do v <- new TwoVar
          on v $ SetA 42
          on v $ SetB 12
          vala <- on v $ GetA
          valb <- on v $ GetB
          delete v
          pure (vala, valb)

