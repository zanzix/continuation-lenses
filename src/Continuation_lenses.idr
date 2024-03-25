infixr 1 |> 

Boundary : Type 
Boundary = (Type, Type) 

Lens : Boundary -> Boundary -> Type 
Lens (x, dx) (y, dy) = ((x -> y), (x, dy) -> dx)

(|>) : Lens (b, db) (c, dc) -> Lens (a, da) (b, db) -> Lens (a, da) (c, dc)
(|>) (get1, set1) (get2, set2) = (get1 . get2, \x => set2 (fst x, set1 (get2 (fst x), snd x)))

-- This is a 'continuation lens'. The right boundary is (a & ¬a)
ContLens : Type -> Type -> Type 
ContLens s a = {k : Type} -> Lens (s, k) (a, a -> k)

-- map for the Cont monad
mapCont : (a -> b) -> (a -> (b -> k) -> k) 
mapCont f = \a, k => k (f a)

-- We have a functor from C to ContLens(C)
mapLens : (a -> b) -> Lens (a, k) (b, b -> k)
mapLens f = (f, uncurry (mapCont f))

-- | Couple of trivial examples
-- lens1 = mapLens (\n => [n])
lens1 : Lens (Nat, k) (List Nat, List Nat -> k)
lens1 = (get, set) where 
  get : Nat -> List Nat 
  get n = [n]
  set : (Nat, (List Nat -> k)) -> k 
  set = uncurry (mapCont get)

-- lens2 = mapLens show
lens2 : Lens (List Nat, k) (String, String -> k)
lens2 = (get, set) where 
  get : List Nat -> String 
  get ns = show ns 
  set : (List Nat, (String -> k)) -> k 
  set = uncurry (mapCont get)

-- escape the Cont moand 
esc : {a, b : _} -> ({k : _} -> a -> (b -> k) -> k) -> a -> b
esc f a = f a id

-- escape the Cont lens
setL : {a : _} -> ({k : _} -> Lens (s, k) (a, a -> k)) -> s -> a
setL lens s = let set = snd lens in set (s, id)

-- extract the continuation and run it
runLens1 : Nat -> List Nat 
runLens1 n = setL lens1 n

runLens2 : List Nat -> String 
runLens2 ns = setL lens2 ns 

-- run the composed lens with const to get the final value 
runComp : Nat -> String
runComp n = let 
  set = (snd (lens2 |> lens1)) 
    in set (n, const)
