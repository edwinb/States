module PList 

import public Data.List

public export
data PList : (Type -> Type) -> Type where
     Nil : PList p
     (::) : p state -> PList p -> PList p

public export
(++) : PList p -> PList p -> PList p
(++) [] ys = ys
(++) (x :: xs) ys = x :: xs ++ ys

public export
appendNilRightNeutral : (l : PList p) -> l ++ [] = l
appendNilRightNeutral [] = Refl
appendNilRightNeutral (x :: xs) = cong (appendNilRightNeutral xs)

public export
data PElem : p state -> PList p -> Type where
     Here : {p : Type -> Type} -> {a : p state} -> PElem {p} a (a :: as)
     There : PElem a as -> PElem a (b :: as)

public export
Uninhabited (PElem {p} x []) where
  uninhabited (Here {p} {a}) impossible

public export
data SubList : PList a -> PList a -> Type where
  SubNil : SubList [] xs
  InList : PElem x ys -> SubList xs ys -> SubList (x :: xs) ys

-- Some useful hints for proof construction in polymorphic programs
%hint
public export total
dropFirst : SubList xs ys -> SubList xs (x :: ys)
dropFirst SubNil = SubNil
dropFirst (InList el sub) = InList (There el) (dropFirst sub)

%hint
public export total
subListId : (xs : PList p) -> SubList xs xs
subListId [] = SubNil
subListId (x :: xs) = InList Here (dropFirst (subListId xs))

public export total
inSuffix : PElem x ys -> SubList xs ys -> PElem x (zs ++ ys)
inSuffix {zs = []} el sub = el
inSuffix {zs = (x :: xs)} el sub = There (inSuffix el sub)

%hint
public export total
dropPrefix : SubList xs ys -> SubList xs (zs ++ ys)
dropPrefix SubNil = SubNil
dropPrefix (InList el sub) = InList (inSuffix el sub) (dropPrefix sub)

public export total
inPrefix : PElem x ys -> SubList xs ys -> PElem x (ys ++ zs)
inPrefix {zs = []} {ys} el sub
    = rewrite appendNilRightNeutral ys in el
inPrefix {zs = (x :: xs)} Here sub = Here
inPrefix {zs = (x :: xs)} (There y) sub = There (inPrefix y SubNil)


