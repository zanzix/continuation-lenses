parameters (r : Type)

  -- cont
  Dual : Type -> Type
  Dual a = a -> r

  Cont : Type -> Type
  Cont a = Dual (Dual a)

  map : (a -> b) -> (Cont a -> Cont b)
  map f e k = e (\a => k (f a))

  ext : (a -> Cont b) -> (Cont a -> Cont b)
  ext f e k = e (\a => f a k)

  bind : Cont a -> (a -> Cont b) -> Cont b
  bind e f = ext f e

  mult : Cont (Cont a) -> Cont a
  mult = ext id

  -- kleisli
  infixr 4 ~>
  (~>) : Type -> Type -> Type
  a ~> b = a -> Cont b

  idk : a ~> a
  idk a k = k a

  seq : a ~> b -> b ~> c -> a ~> c
  seq f g = ext g . f

  -- coexponentials
  (<=) : Type -> Type -> Type
  a <= b = (b, Dual a)

  cocurry : (a <= b ~> c) -> (b ~> Either a c)
  cocurry f b k =
    let k1 = k . Left
        k2 = k . Right
    in f (b, k1) k2

  councurry : (b ~> Either a c) -> (a <= b ~> c)
  councurry f (b , k1) k2 = f b (either k1 k2)

  colam : (Dual a ~> b) -> (Unit ~> Either a b)
  colam f = cocurry (uncurry (\_ => f))

  coapp : (Unit ~> Either a b) -> (Dual a ~> b)
  coapp f = curry (councurry f) ()

  tnd : Unit ~> Either a (Dual a)
  tnd = colam idk

  swap : Either a b -> Either b a
  swap = either Right Left

  adj : (Dual a ~> b) -> (Dual b ~> a)
  adj f = coapp (\_ => map swap (colam f ()))

  dne : Dual (Dual a) ~> a
  dne = adj idk

  -- TODO: prove deMorgan's laws

  -- Lawvere's boundary operator
  Del : Type -> Type
  Del a = a <= a

  -- TODO: differential structure using deMorgan's laws
