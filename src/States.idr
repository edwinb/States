module States

import public Utils.PList

public export
SM_sig : Type -> Type
SM_sig state = (t : Type) -> state -> (t -> state) -> Type

public export 
%error_reverse
record SM stateType where
  constructor MkSM
  init       : stateType
  final      : stateType -> Type
  operations : SM_sig stateType

public export
interface Execute (sm : SM state) (m : Type -> Type) where
     resource : state -> Type
     initialise : resource (init sm)

     covering
     exec : (res : resource in_state) -> 
            (ops : operations sm ty in_state out_fn) -> 
            (k : (x : ty) -> resource (out_fn x) -> m a) -> m a


public export
data Resource : SM state -> Type where
     MkRes : label -> (sm : SM state) -> state -> Resource sm

infix 5 :::

%error_reverse
public export
(:::) : label -> (p : (SM state, state)) -> Resource (fst p)
(:::) lbl (sm, st) = MkRes lbl sm st

public export
data State : SM state -> Type where
     MkState : State r


-- This needs to be a specialised type, rather than a generic List,
-- because resources might contain List as a type, and we'd end up with
-- a universe cycle.
namespace Context
  public export
  data Context : PList SM -> Type where
       Nil : Context []
       (::) : Resource t -> Context ts -> Context (t :: ts)

  public export
  (++) : Context ts -> Context us -> Context (ts ++ us)
  (++) [] ys = ys
  (++) (x :: xs) ys = x :: xs ++ ys

public export
appendNilRightNeutral : (l : Context ts) -> l ++ [] = l
appendNilRightNeutral [] = Refl
appendNilRightNeutral (x :: xs) = rewrite appendNilRightNeutral xs in Refl

public export
data HasIFace : state -> (sm : SM state) -> State r -> Context ts -> Type where
     Here : HasIFace st sm lbl (MkRes lbl sm st :: rs)
     There : HasIFace st sm lbl rs -> HasIFace st sm lbl (r :: rs)

public export
updateCtxt : {st : state} ->
             (ctxt : Context ts) -> 
             HasIFace st sm lbl ctxt -> state -> Context ts
updateCtxt ((MkRes lbl st _) :: rs) Here val = ((MkRes lbl st val) :: rs)
updateCtxt (r :: rs) (There x) ty = r :: updateCtxt rs x ty

public export
dropType : (ts : PList SM) -> (ctxt : Context ts) ->
           HasIFace st sm lbl ctxt -> PList SM
dropType (sm :: ts) (MkRes lbl sm st :: xs) Here = ts
dropType (t :: ts) (x :: xs) (There p) = t :: dropType ts xs p

public export
drop : (ctxt : Context ts) -> (prf : HasIFace st sm lbl ctxt) -> 
       Context (dropType ts ctxt prf)
drop ((MkRes lbl sm st) :: rs) Here = rs
drop (r :: rs) (There p) = r :: drop rs p

public export
data ElemCtxt : Resource t -> Context ts -> Type where
     HereCtxt : ElemCtxt a (a :: as)
     ThereCtxt : ElemCtxt a as -> ElemCtxt a (b :: as)

public export
data SubCtxt : Context ts -> Context us -> Type where
  SubNil : SubCtxt [] xs
  InCtxt : ElemCtxt x ys -> SubCtxt xs ys -> SubCtxt (x :: xs) ys

Uninhabited (ElemCtxt x []) where
  uninhabited HereCtxt impossible
  uninhabited (ThereCtxt _) impossible

public export total 
updateAt : {xs : Context ts} ->
           {val : ty} ->
           (idx : ElemCtxt (MkRes lbl sm val) xs) -> 
           (a : ty) -> Context ts -> Context ts
updateAt HereCtxt a (MkRes lbl ops val :: xs) = MkRes lbl ops a :: xs
updateAt (ThereCtxt p) a (x :: xs) = x :: updateAt p a xs

public export total 
updateWith : {ys : Context ts} ->
             (ys' : Context ts) -> (xs : Context us) ->
             SubCtxt ys xs -> Context us
updateWith [] xs prf = xs
updateWith (MkRes lbl f a :: ys) xs (InCtxt {x = MkRes _ _ _} idx rest) 
     = let rec = updateWith ys xs rest in
           updateAt idx a (updateWith ys xs rest)

export
data SMs : (m : Type -> Type) ->
           (ty : Type) ->
           PList SM ->
           Context ts -> (ty -> Context us) ->
           Type where
     Pure : (result : val) -> SMs m val ops (out_fn result) out_fn
     Bind : SMs m a ops st1 st2_fn ->
            ((result : a) -> SMs m b ops (st2_fn result) st3_fn) ->
            SMs m b ops st1 st3_fn
     Lift : Monad m => m t -> SMs m t ops ctxt (const ctxt)

     New : (sm : SM state) ->
           {auto prf : PElem sm ops} ->
           SMs m (State sm) ops ctxt 
                    (\lbl => MkRes lbl sm (init sm) :: ctxt)
     Delete : (lbl : State iface) -> 
              {auto prf : HasIFace st sm lbl ctxt} ->
              {auto finalok : final sm st} ->
              SMs m () ops ctxt (const (drop ctxt prf))

     On : (lbl : State sm) ->
          {auto prf : HasIFace in_state sm lbl ctxt} ->
          (op : operations sm t in_state out_fn) ->
          SMs m t ops ctxt (\res => updateCtxt ctxt prf (out_fn res))
     Call : {auto op_prf : SubList ops' ops} -> 
            SMs m t ops' ys ys' ->
            {auto ctxt_prf : SubCtxt ys xs} ->
            SMs m t ops xs (\result => updateWith (ys' result) xs ctxt_prf)

public export
data Action : Type -> Type where
     Stable : label -> (SM state, state) -> Action ty
     Trans : label -> (SM state, state) -> (ty -> state) -> Action ty
     Add : label -> (SM state, state) -> Action ty
     Remove : label -> (SM state, state) -> Action ty

public export
SMTransNew : (m : Type -> Type) ->
             (ty : Type) -> 
             (ops : PList SM) ->
             List (Action ty) -> Type
SMTransNew m ty ops xs 
     = SMs m ty ops (in_res xs) (\result : ty => out_res result xs)
  where
    ctxt : (input : Bool) -> List (Action ty) -> PList SM
    ctxt inp [] = []
    ctxt inp (Stable lbl (sig, inr) :: xs) = sig :: ctxt inp xs
    ctxt inp (Trans lbl (sig, inr) outr :: xs) = sig :: ctxt inp xs
    ctxt inp (Add lbl (sig, inr) :: xs) = if inp then ctxt inp xs
                                                 else sig :: ctxt inp xs
    ctxt inp (Remove lbl (sig, inr) :: xs) = if inp then sig :: ctxt inp xs
                                                    else ctxt inp xs

    out_res : ty -> (as : List (Action ty)) -> Context (ctxt False as)
    out_res x [] = []
    out_res x (Stable lbl (sig, inr) :: xs) = MkRes lbl sig inr :: out_res x xs
    out_res x (Trans lbl (sig, inr) outr :: xs) 
                                    = MkRes lbl sig (outr x) :: out_res x xs
    out_res x (Add lbl (sig, inr) :: xs) = MkRes lbl sig inr :: out_res x xs
    out_res x (Remove lbl (sig, inr) :: xs) = out_res x xs

    in_res : (as : List (Action ty)) -> Context (ctxt True as)
    in_res [] = []
    in_res (Stable lbl (sig, inr) :: xs) = MkRes lbl sig inr :: in_res xs
    in_res (Trans lbl (sig, inr) outr :: xs) = MkRes lbl sig inr :: in_res xs
    in_res (Add lbl (sig, inr) :: xs) = in_res xs
    in_res (Remove lbl (sig, inr) :: xs) = MkRes lbl sig inr :: in_res xs

public export
SMTrans : (m : Type -> Type) -> (ty : Type) -> List (Action ty) -> Type
SMTrans m ty xs 
     = SMTransNew m ty [] xs

public export
SMNew : (m : Type -> Type) -> (ty : Type) -> (ops : PList SM) -> Type
SMNew m ty ops = SMTransNew m ty ops []

public export
SMOp : (m : Type -> Type) -> Type -> Type
SMOp m ty = {ts : _ } -> {ops : _} -> {ctxt : Context ts} -> 
            SMs m ty ops ctxt (const ctxt)

-- Some useful hints for proof construction in polymorphic programs
%hint
public export total
dropFirst : SubCtxt xs ys -> SubCtxt xs (x :: ys)
dropFirst SubNil = SubNil
dropFirst (InCtxt el sub) = InCtxt (ThereCtxt el) (dropFirst sub)

%hint
public export total
subListId : (xs : Context ts) -> SubCtxt xs xs
subListId [] = SubNil
subListId (x :: xs) = InCtxt HereCtxt (dropFirst (subListId xs))

public export total
inSuffix : ElemCtxt x ys -> SubCtxt xs ys -> ElemCtxt x (zs ++ ys)
inSuffix {zs = []} el sub = el
inSuffix {zs = (x :: xs)} el sub = ThereCtxt (inSuffix el sub)

%hint
public export total
dropPrefix : SubCtxt xs ys -> SubCtxt xs (zs ++ ys)
dropPrefix SubNil = SubNil
dropPrefix (InCtxt el sub) = InCtxt (inSuffix el sub) (dropPrefix sub)

public export total
inPrefix : ElemCtxt x ys -> SubCtxt xs ys -> ElemCtxt x (ys ++ zs)
inPrefix {zs = []} {ys} el sub
    = rewrite appendNilRightNeutral ys in el
inPrefix {zs = (x :: xs)} HereCtxt sub = HereCtxt
inPrefix {zs = (x :: xs)} (ThereCtxt y) sub = ThereCtxt (inPrefix y SubNil)

%hint
public export total
dropSuffix : SubCtxt xs ys -> SubCtxt xs (ys ++ zs)
dropSuffix SubNil = SubNil
dropSuffix (InCtxt el sub) = InCtxt (inPrefix el sub) (dropSuffix sub)


export
pure : (x : val) -> SMs m val ops (out_fn x) out_fn
pure = Pure

export
lift : Monad m => m t -> SMs m t ops ctxt (const ctxt)
lift = Lift

export
new : (sm : SM state) ->
      {auto prf : PElem sm ops} ->
      SMs m (State sm) ops ctxt 
              (\lbl => MkRes lbl sm (init sm) :: ctxt)
new = New

export
delete : (lbl : State iface) -> 
         {auto prf : HasIFace st sm lbl ctxt} ->
         {auto finalok : final sm st} ->
         SMs m () ops ctxt (const (drop ctxt prf))
delete = Delete

export
on : (lbl : State sm) ->
     {auto prf : HasIFace in_state sm lbl ctxt} ->
     (op : operations sm t in_state out_fn) ->
     SMs m t ops ctxt (\res => updateCtxt ctxt prf (out_fn res))
on = On

export
call : {auto op_prf : SubList ops' ops} -> 
       SMs m t ops' ys ys' ->
       {auto ctxt_prf : SubCtxt ys xs} ->
       SMs m t ops xs (\result => updateWith (ys' result) xs ctxt_prf)
call = Call

export
(>>=) : SMs m a ops st1 st2_fn ->
        ((x : a) -> SMs m b ops (st2_fn x) st3_fn) ->
        SMs m b ops st1 st3_fn
(>>=) = Bind


public export
interface Transform (sm : SM state) (sm' : SM state')
                    (ops : PList SM)
                    (m : Type -> Type) | sm, m where
    -- Explain how our state corresponds to the inner machine's state
    toState : state -> state'
    -- Make sure the initial and final states correspond. 
    initOK : init sm' = toState (init sm) -- 'Refl' should usually work
    finalOK : (x : state) -> final sm x -> final sm' (toState x)

    -- Implement our operations in terms of the inner operations
    transform : (lbl : State sm') ->
                (op : operations sm t in_state tout_fn) ->
                SMs m t ops [MkRes lbl sm' (toState in_state)]
                   (\result => [MkRes lbl sm' (toState (tout_fn result))])

namespace Env
  public export
  data Env : (m : Type -> Type) -> Context ts -> Type where
       Nil : Env m []
       (::) : (exec : Execute sm m) => 
              resource @{exec} a -> Env m xs -> Env m (MkRes lbl sm a :: xs)

namespace Execs
  public export
  data Execs : (m : Type -> Type) -> PList SM -> Type where
       Nil : Execs m []
       (::) : Execute res m -> Execs m xs -> Execs m (res :: xs)

dropVal : (prf : HasIFace st sm lbl ctxt) ->
          Env m ctxt -> Env m (drop ctxt prf)
dropVal Here (x :: xs) = xs
dropVal (There p) (x :: xs) = x :: dropVal p xs

envElem : ElemCtxt x xs -> Env m xs -> Env m [x]
envElem HereCtxt (x :: xs) = [x]
envElem (ThereCtxt p) (x :: xs) = envElem p xs

dropEnv : Env m ys -> SubCtxt xs ys -> Env m xs
dropEnv [] SubNil = []
dropEnv (x :: xs) SubNil = []
dropEnv [] (InCtxt idx rest) = absurd idx
dropEnv (x :: xs) (InCtxt idx rest) 
    = let [e] = envElem idx (x :: xs) in
          e :: dropEnv (x :: xs) rest

getExecute : (execs : Execs m rs) -> (pos : PElem sm rs) -> 
             Execute sm m
getExecute (h :: hs) Here = h
getExecute (h :: hs) (There p) = getExecute hs p


execsElem : PElem x xs -> Execs m xs -> Execs m [x]
execsElem Here (x :: xs) = [x]
execsElem (There p) (x :: xs) = execsElem p xs

dropExecs : Execs m ys -> SubList xs ys -> Execs m xs
dropExecs [] SubNil = []
dropExecs [] (InList idx rest) = absurd idx
dropExecs (x :: xs) SubNil = []
dropExecs (x :: xs) (InList idx rest) 
    = let [e] = execsElem idx (x :: xs) in
          e :: dropExecs (x :: xs) rest

getEnvExecute : {xs, ys : Context ts} ->
                ElemCtxt (MkRes lbl sm val) xs -> Env m ys -> Execute sm m
getEnvExecute HereCtxt (h :: hs) = %implementation
getEnvExecute (ThereCtxt p) (h :: hs) = getEnvExecute p hs

replaceEnvAt : (exec : Execute sm m) =>
               {xs, ys : Context ts} ->
               (idx : ElemCtxt (MkRes lbl sm val) xs) -> 
               (env : Env m ys) ->
               (resource @{exec} st) ->
               Env m (updateAt idx st ys)
replaceEnvAt @{exec} HereCtxt (y :: ys) x = (::) @{exec} x ys
replaceEnvAt (ThereCtxt p) (y :: ys) x = y :: replaceEnvAt p ys x

rebuildEnv : {ys, ys' : Context ts} ->
             Env m ys' -> (prf : SubCtxt ys inr) -> Env m inr ->
             Env m (updateWith ys' inr prf)
rebuildEnv [] SubNil env = env
rebuildEnv ((::) {a} res xs) (InCtxt {x = MkRes lbl sm val} idx rest) env 
      = replaceEnvAt idx (rebuildEnv xs rest env) res

private
execRes : Env m ctxt ->
          (prf : HasIFace in_state sm lbl ctxt) ->
          (op : operations sm t in_state out_fn) ->
          ((x : t) -> Env m (updateCtxt ctxt prf (out_fn x)) -> m b) ->
          m b
execRes {sm} {in_state} {out_fn} (val :: env) Here op k 
  = exec {sm} {in_state} {out_fn} val op (\v, res => k v (res :: env))
execRes {sm} {in_state} {out_fn} (val :: env) (There p) op k 
  = execRes {sm} {in_state} {out_fn} env p op (\v, env' => k v (val :: env'))

export total
runSMs : Env m inr -> Execs m ops ->
            SMs m a ops inr outfn ->
            ((x : a) -> Env m (outfn x) -> m b) -> m b
runSMs env execs (Pure x) k = k x env
runSMs env execs (Bind prog next) k 
     = runSMs env execs prog (\prog', env' => runSMs env' execs (next prog') k)
runSMs env execs (Lift action) k 
     = do res <- action
          k res env
runSMs env execs (New {prf} sm) k 
     = let h = getExecute execs prf
           res = initialise @{h} in
           k MkState (res :: env)
runSMs env execs (Delete {prf} lbl) k 
     = k () (dropVal prf env)
runSMs env execs (On {prf} lbl op) k 
     = execRes env prf op k
runSMs env execs (Call {op_prf} prog {ctxt_prf}) k 
     = let env' = dropEnv env ctxt_prf 
           execs' = dropExecs execs op_prf in
           runSMs env' execs' prog 
               (\prog', envk => k prog' (rebuildEnv envk ctxt_prf env))

public export
interface ExecList (m : Type -> Type) (ops : PList SM) where
  mkExecs : Execs m ops

export
ExecList m [] where
  mkExecs = []

export
(Execute res m, ExecList m xs) => ExecList m (res :: xs) where
  mkExecs = %implementation :: mkExecs

headEnvType : {sm : SM state} ->
              Env m [MkRes v sm x] -> Execute sm m
headEnvType {sm} {m} {x} (h :: hs) = %implementation 

headEnv : (env : Env m [MkRes v sm x]) -> resource @{headEnvType env} x
headEnv (x :: xs) = x

-- Yuck. Especially the 'believe_me'. Given that at this stage there is only
-- one possibility for the inner 'Execute', because it's a generic thing we
-- have to pass in and there's no way of changing it in 'runSMs', this
-- is currently fine. But: how to convince Idris? And will it always be fine?
-- What if we change 'runSMs'?
using (sm : SM state, sm' : SM state')
  export
  %overlapping -- It's not really, because of the superinterface, 
               -- but the check isn't good enough for this yet
  (trans : Transform sm sm' ops m, 
   ExecList m ops,
   lower : Execute sm' m) => Execute sm m where
     resource @{trans} @{_} @{lower} x = resource @{lower} (toState @{trans} x)
     initialise @{trans} @{_} @{lower}
           = rewrite sym (initOK @{trans}) in 
                     initialise @{lower}

     exec @{trans} @{_} @{lower} {out_fn} res op k = 
       runSMs [res] mkExecs (transform {sm} {m} {tout_fn=out_fn} MkState op) 
       (\result, env => let env' = headEnv env in k result (believe_me env'))

export total
run : Monad m => 
      {auto execs : Execs m ops} -> SMs m a ops [] (const []) -> 
      m a
run {execs} prog = runSMs [] execs prog (\res, env' => pure res)
