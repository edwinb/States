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
  creators   : SM_sig stateType 

-- As a data type, helps with error_reverse and type class search, but
-- really it's just Void
public export
data None : {stateType : Type} -> SM_sig stateType where
     NoCmd : {a : stateType} -> Void -> None {stateType} () a (\res => a)

export
pass : None {stateType} ty ins outf -> a
pass (NoCmd p) = void p

public export
interface Execute (sm : SM state) (m : Type -> Type) where
    resource : state -> Type
    initialise : resource (init sm)

    covering
    exec : (res : resource in_state) -> 
           (ops : operations sm ty in_state out_fn) -> 
           (k : (x : ty) -> resource (out_fn x) -> m a) -> m a
    
    covering
    create : (res : resource in_state) ->
             (ops : creators sm ty in_state out_fn) ->
             (k : (x : ty) -> resource (out_fn x) -> m a) -> m a

public export
data State : SM state -> Type where
     MkState : State sm

public export
data Resource : SM state -> Type where
     MkRes : label -> (sm : SM state) -> state -> Resource sm

infix 5 :::

%error_reverse
public export
(:::) : {sm : SM state} -> State sm -> (p : state) -> Resource sm
(:::) {sm} lbl st = MkRes lbl sm st


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
data InState : (sm : SM state) -> State r -> state -> Context ts -> Type where
     Here : InState sm lbl st (MkRes lbl sm st :: rs)
     There : InState sm lbl st rs -> InState sm lbl st (r :: rs)

public export
updateCtxt : {st : state} ->
             (ctxt : Context ts) -> 
             InState sm lbl st ctxt -> state -> Context ts
updateCtxt ((MkRes lbl st _) :: rs) Here val = ((MkRes lbl st val) :: rs)
updateCtxt (r :: rs) (There x) ty = r :: updateCtxt rs x ty

public export
dropType : (ts : PList SM) -> (ctxt : Context ts) ->
           InState sm lbl st ctxt -> PList SM
dropType (sm :: ts) (MkRes lbl sm st :: xs) Here = ts
dropType (t :: ts) (x :: xs) (There p) = t :: dropType ts xs p

public export
drop : (ctxt : Context ts) -> (prf : InState sm lbl st ctxt) -> 
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
data SMProg : (m : Type -> Type) ->
           (ty : Type) ->
           PList SM ->
           Context ts -> (ty -> Context us) ->
           Type where
     Pure : (result : val) -> SMProg m val ops (out_fn result) out_fn
     Bind : SMProg m a ops st1 st2_fn ->
            ((result : a) -> SMProg m b ops (st2_fn result) st3_fn) ->
            SMProg m b ops st1 st3_fn
     Lift : Monad m => m t -> SMProg m t ops ctxt (const ctxt)

     New : (sm : SM state) ->
           {auto prf : PElem sm ops} ->
           SMProg m (State sm) ops ctxt 
                    (\lbl => MkRes lbl sm (init sm) :: ctxt)
     Delete : (lbl : State iface) -> 
              {auto prf : InState sm lbl st ctxt} ->
              {auto finalok : final sm st} ->
              SMProg m () ops ctxt (const (drop ctxt prf))

     On : (lbl : State sm) ->
          {auto prf : InState sm lbl in_state ctxt} ->
          (op : operations sm t in_state out_fn) ->
          SMProg m t ops ctxt (\res => updateCtxt ctxt prf (out_fn res))
     NewFrom : (lbl : State sm) ->
               {auto prf : InState sm lbl in_state ctxt} ->
               (op : creators sm t in_state out_fn) ->
               SMProg m (t, State sm)
                     ops ctxt (\res => MkRes (snd res) sm (out_fn (fst res)) :: ctxt)
     Call : {auto op_prf : SubList ops' ops} -> 
            SMProg m t ops' ys ys' ->
            {auto ctxt_prf : SubCtxt ys xs} ->
            SMProg m t ops xs (\result => updateWith (ys' result) xs ctxt_prf)

using (sm : SM st)
  public export
  data Action : Type -> Type where
       Stable : State sm -> st -> Action ty
       Trans : State sm -> st -> (ty -> st) -> Action ty
       Add : State sm -> st -> Action ty
       Remove : State sm -> st -> Action ty

public export
SMs : (m : Type -> Type) ->
      (ty : Type) -> 
      (ops : PList SM) ->
      List (Action ty) -> Type
SMs m ty ops xs 
     = SMProg m ty ops (in_res xs) (\result : ty => out_res result xs)
  where
    ctxt : (input : Bool) -> List (Action ty) -> PList SM
    ctxt inp [] = []
    ctxt inp (Stable {sm} lbl inr :: xs) = sm :: ctxt inp xs
    ctxt inp (Trans {sm} lbl inr outr :: xs) = sm :: ctxt inp xs
    ctxt inp (Add {sm} lbl inr :: xs) = if inp then ctxt inp xs
                                               else sm :: ctxt inp xs
    ctxt inp (Remove {sm} lbl inr :: xs) = if inp then sm :: ctxt inp xs
                                                  else ctxt inp xs

    out_res : ty -> (as : List (Action ty)) -> Context (ctxt False as)
    out_res x [] = []
    out_res x (Stable {sm} lbl inr :: xs) = MkRes lbl sm inr :: out_res x xs
    out_res x (Trans {sm} lbl inr outr :: xs) 
                                    = MkRes lbl sm (outr x) :: out_res x xs
    out_res x (Add {sm} lbl inr :: xs) = MkRes lbl sm inr :: out_res x xs
    out_res x (Remove {sm} lbl inr :: xs) = out_res x xs

    in_res : (as : List (Action ty)) -> Context (ctxt True as)
    in_res [] = []
    in_res (Stable {sm} lbl inr :: xs) = MkRes lbl sm inr :: in_res xs
    in_res (Trans {sm} lbl inr outr :: xs) = MkRes lbl sm inr :: in_res xs
    in_res (Add {sm} lbl inr :: xs) = in_res xs
    in_res (Remove {sm} lbl inr :: xs) = MkRes lbl sm inr :: in_res xs

public export
SMTrans : (m : Type -> Type) -> (ty : Type) -> List (Action ty) -> Type
SMTrans m ty xs 
     = SMs m ty [] xs

public export
SMNew : (m : Type -> Type) -> (ty : Type) -> (ops : PList SM) -> Type
SMNew m ty ops = SMs m ty ops []

public export
SMOp : (m : Type -> Type) -> Type -> Type
SMOp m ty = {ts : _ } -> {ops : _} -> {ctxt : Context ts} -> 
            SMProg m ty ops ctxt (const ctxt)

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
pure : (x : val) -> SMProg m val ops (out_fn x) out_fn
pure = Pure

export
lift : Monad m => m t -> SMProg m t ops ctxt (const ctxt)
lift = Lift

export
new : (sm : SM state) ->
      {auto prf : PElem sm ops} ->
      SMProg m (State sm) ops ctxt 
              (\lbl => MkRes lbl sm (init sm) :: ctxt)
new = New

export
delete : (lbl : State iface) -> 
         {auto prf : InState sm lbl st ctxt} ->
         {auto finalok : final sm st} ->
         SMProg m () ops ctxt (const (drop ctxt prf))
delete = Delete

export
on : (lbl : State sm) ->
     {auto prf : InState sm lbl in_state ctxt} ->
     (op : operations sm t in_state out_fn) ->
     SMProg m t ops ctxt (\res => updateCtxt ctxt prf (out_fn res))
on = On
    
export
newFrom : (lbl : State sm) ->
       {auto prf : InState sm lbl in_state ctxt} ->
       (op : creators sm t in_state out_fn) ->
       SMProg m (t, State sm)
             ops ctxt (\ res => MkRes (snd res) sm (out_fn (fst res)) :: ctxt) 
newFrom = NewFrom
     
export
call : {auto op_prf : SubList ops' ops} -> 
       SMProg m t ops' ys ys' ->
       {auto ctxt_prf : SubCtxt ys xs} ->
       SMProg m t ops xs (\result => updateWith (ys' result) xs ctxt_prf)
call = Call

export
(>>=) : SMProg m a ops st1 st2_fn ->
        ((x : a) -> SMProg m b ops (st2_fn x) st3_fn) ->
        SMProg m b ops st1 st3_fn
(>>=) = Bind

public export
stateTypes : PList SM -> Type
stateTypes [] = ()
stateTypes ((::) {state} x []) = state
stateTypes ((::) {state} x (y :: xs)) = (state, stateTypes (y :: xs))

public export
initStates : (sms : PList SM) -> stateTypes sms
initStates [] = ()
initStates (x :: []) = init x 
initStates (x :: (y :: xs)) = (init x, initStates (y :: xs))

public export
Labels : PList SM -> Type
Labels [] = ()
Labels (x :: []) = State x
Labels (x :: (y :: xs)) = (State x, Labels (y :: xs))

public export
mkRes : Labels sms -> stateTypes sms -> Context sms
mkRes {sms = []} () () = []
mkRes {sms = (sm :: [])} l t = MkRes l sm t :: []
mkRes {sms = (sm :: sm' :: sms)} (l, ls) (t, ts) 
      = MkRes l sm t :: mkRes ls ts

public export
AllFinal : (sms : _) -> stateTypes sms -> Type
AllFinal [] x = ()
AllFinal (sm :: []) st = final sm st
AllFinal (sm :: z :: zs) (st, sts) = (final sm st, AllFinal _ sts)

public export
interface Transform (sm : SM state) (sms' : PList SM)
                    (ops : PList SM)
                    (m : Type -> Type) | sm, m where
    -- Explain how our state corresponds to the inner machine's state
    toState : state -> stateTypes sms'

    -- Make sure the initial and final states correspond. 
    initOK : initStates sms' = toState (init sm) -- 'Refl' should usually work

    finalOK : (x : state) -> (prf : final sm x) -> AllFinal sms' (toState x)

    -- Implement our operations in terms of the inner operations
    execAs : (lbls : Labels sms') -> -- State sm') ->
             (op : operations sm t in_state tout_fn) ->
             SMProg m t ops (mkRes lbls (toState in_state))
                (\result => (mkRes lbls (toState (tout_fn result))))

    createAs : (lbls : Labels sms') -> -- State sm') ->
               (op : creators sm t in_state tout_fn) ->
               SMProg m (Labels sms', t) ops (mkRes lbls (toState in_state))
                  (\result => 
                    (mkRes (fst result) (toState (tout_fn (snd result))))
                      ++
                    (mkRes lbls (toState in_state)))

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

dropVal : (prf : InState sm lbl st ctxt) ->
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
getExecute (_ :: hs) (There p) = getExecute hs p

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

getIFaceExecute : InState sm lbl in_state ctxt ->
                  Env m ctxt -> Execute sm m
getIFaceExecute Here (h :: hs) = %implementation
getIFaceExecute (There p) (h :: hs) = getIFaceExecute p hs

lookupEnv : (i : InState sm lbl in_state ctxt) ->
            (env : Env m ctxt) -> 
            (resource @{getIFaceExecute i env} in_state)
lookupEnv Here (h :: hs) = h
lookupEnv (There p) (h :: hs) = lookupEnv p hs


private
execRes : Env m ctxt ->
          (prf : InState sm lbl in_state ctxt) ->
          (op : operations sm t in_state out_fn) ->
          ((x : t) -> Env m (updateCtxt ctxt prf (out_fn x)) -> m b) ->
          m b
execRes {sm} {in_state} {out_fn} (val :: env) Here op k 
  = exec {sm} {in_state} {out_fn} val op (\v, res => k v (res :: env))
execRes {sm} {in_state} {out_fn} (val :: env) (There p) op k 
  = execRes {sm} {in_state} {out_fn} env p op (\v, env' => k v (val :: env'))

-- private
-- createRes : Env m ctxt ->
--             (op : creators sm t in_state out_fn) ->
--             ((x : (t, State sm)) -> 
--                 Env m (MkRes (snd x) sm (out_fn (fst x)) :: ctxt) -> m b) ->
--             m b
-- execRes {sm} {in_state} {out_fn} (val :: env) Here op k 
--   = exec {sm} {in_state} {out_fn} val op (\v, res => k v (res :: env))
-- execRes {sm} {in_state} {out_fn} (val :: env) (There p) op k 
--   = execRes {sm} {in_state} {out_fn} env p op (\v, env' => k v (val :: env'))

export total
runSMs : Env m inr -> Execs m ops ->
            SMProg m a ops inr outfn ->
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
runSMs env execs (NewFrom {sm} {in_state} {out_fn} {prf} lbl op) k 
     = let envItem = lookupEnv prf env 
           h = getIFaceExecute prf env in
           create {sm} {out_fn} {in_state}
                  envItem op (\val, res => k (val, MkState) 
                                      (res :: env))
runSMs env execs (Call {op_prf} prog {ctxt_prf}) k 
     = let env' = dropEnv env ctxt_prf 
           execs' = dropExecs execs op_prf in
           runSMs env' execs' prog 
               (\prog', envk => k prog' (rebuildEnv envk ctxt_prf env))


public export
interface ExecList (m : Type -> Type) (ops : PList SM) where
  constructor MkExecList
  mkExecs : Execs m ops

export total
run : (Applicative m, ExecList m ops) => 
      SMProg m a ops [] (const []) -> 
      m a
run prog = runSMs [] mkExecs prog (\res, env' => pure res)

export total
runPure : ExecList Basics.id ops =>
          SMProg Basics.id a ops [] (const []) -> a
runPure prog = runSMs [] mkExecs prog (\res, env' => res)

export
ExecList m [] where
  mkExecs = []

export
(Execute res m, ExecList m xs) => ExecList m (res :: xs) where
  mkExecs = %implementation :: mkExecs

firstExec : ExecList m (res :: xs) -> Execute res m
firstExec x with (mkExecs @{x})
  firstExec x | (y :: ys) = y

mkExecList : Execs m ops -> ExecList m ops
mkExecList {ops = []} x = %implementation
mkExecList {ops = (y :: ys)} (h :: xs) 
       = let rec = mkExecList xs in %implementation

tailExec : ExecList m (res :: xs) -> ExecList m xs
tailExec es with (mkExecs @{es})
  tailExec es | (y :: ys) = mkExecList ys

{- Yuck. What follows is largely write only code, but at least it type checks.

There is, however, a 'believe_me' in envRes. Given that at this stage there is
only one possibility for the inner 'Execute', because it's a generic thing we
have to pass in and there's no way of changing it in 'runSMs', this is
currently fine. But: how to convince Idris? And will it always be fine?  What
if we change 'runSMs'?  
-}

resources : (sms : _) -> ExecList m sms -> stateTypes sms -> Type
resources [] es st = ()
resources (x :: []) es st = resource @{firstExec es} st
resources (x :: (y :: ys)) es (st, sts)
     = (resource @{firstExec es} st, resources (y :: ys) @{tailExec es} sts)

initAll : (sms : _) -> 
          (es : ExecList m sms) -> resources sms es (initStates sms)
initAll [] es = ()
initAll (x :: []) es = initialise {sm=x} @{firstExec es} 
initAll (x :: (y :: ys)) es 
    = (initialise {sm=x} @{firstExec es}, initAll (y :: ys) (tailExec es))

resCtxt : (sms : _) -> (sts : stateTypes sms) -> Context sms
resCtxt [] sts = []
resCtxt (sm :: []) st = [MkRes (MkState {sm}) sm st]
resCtxt (sm :: (y :: ys)) (st, sts) 
    = MkRes (MkState {sm}) sm st :: resCtxt _ sts

resEnv : {lower : ExecList m sms} ->
         (lbls : _) ->
         (res : resources sms lower sts) -> Env m (mkRes lbls sts)
resEnv {sms = []} {sts = ()} () res = []
resEnv {lower} {sms = (x :: [])} {sts} lbls res 
       = (::) @{firstExec lower} res []
resEnv {lower = lower} {sts = (st, sts)} {sms = (x :: y :: ys)} 
       (lbl, lbls) (res, rest) 
       = (::) @{firstExec lower} res (resEnv lbls rest)

mkLabels : (sms : _) -> Labels sms
mkLabels [] = ()
mkLabels (x :: []) = MkState
mkLabels (x :: y :: ys) = (MkState, mkLabels (y :: ys))

envRes : {ctxt : Context sms} ->
         Env m ctxt -> resources sms lower sts
envRes [] = ()
envRes (y :: []) = believe_me y
envRes {m} ((::) {m} y ((::) {sm} {m} {a} {lbl} z zs)) {sts = (st, sts)} 
     = (believe_me y, envRes {m} ((::) {sm} {m} {a} {lbl} z zs))

take : {ctxt : Context sms} -> {ctxt' : Context sms'} ->
       Env m (ctxt ++ ctxt') -> Env m ctxt
take {ctxt = []} env = []
take {ctxt = (_ :: hs)} (x :: env) = x :: take env

using (sm : SM state, sms' : PList SM)
  export
  %overlapping -- It's not really, because of the superinterface, 
               -- but the check isn't good enough for this yet
  (trans : Transform sm sms' ops m, 
   ExecList m ops,
   lower : ExecList m sms') => Execute sm m where
     resource @{trans} @{_} @{lower} {sms'} x 
         = resources sms' lower (toState @{trans} x)
     initialise @{trans} @{_} @{lower} {sms'}
           = rewrite sym (initOK @{trans}) in 
                initAll sms' lower -- (initStates sms')

     exec @{trans} @{_} @{lower} {out_fn} {sms'} res op k = 
             let env = resEnv (mkLabels sms') res in
                 runSMs env mkExecs 
                    (execAs {sm} {m} {tout_fn=out_fn} (mkLabels sms') op)
                    (\result, envk => k result (envRes envk))

     create @{trans} @{_} @{lower} {out_fn} {sms'} res op k = -- ?foo -- void (noCreators @{nocreate} op)
             let env = resEnv (mkLabels sms') res in
                 runSMs env mkExecs 
                    (createAs {sm} {m} {tout_fn=out_fn} (mkLabels sms') op)
                    (\result, envk => k (snd result) (envRes (take envk)))
