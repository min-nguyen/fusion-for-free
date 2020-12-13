{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

data Free f a where
   Var :: a -> Free f a
   Con :: f (Free f a) -> Free f a

fold :: Functor f => (f b -> b) -> (a -> b) -> (Free f a -> b)
fold alg gen (Var x)  = gen x
fold alg gen (Con op) = alg (fmap (fold alg gen) op)

instance Functor f => Functor (Free f) where
   fmap g (Var x)  = Var (g x)
   fmap g (Con fx) = Con (fmap (fmap g) fx)

-- Free f (a -> b) <*> Free f a
instance Functor f => Applicative (Free f) where
   pure = Var
   -- f   :: (a -> b)               as :: Free f a
   Var f   <*> as = fmap f as
   -- faf :: f (Free f (a -> b))    as :: Free f a
   -- We extract the function Free f (a -> b) using fmap, and then
   -- apply the function (a -> b) using <*>
   Con faf <*> as = Con (fmap  (<*> as)   faf)

instance Functor f => Monad (Free f) where
   return x = Var x
   m >>= f  = fold Con f m

-- | Non-determinism
data Nondet k where
   Or :: k -> k -> Nondet k

instance Functor Nondet where
   fmap f (Or x y) = Or (f x) (f y)

coin :: Free Nondet Bool
coin = Con (Or (Var True) (Var False))

-- | General handler
--   handle :: Free F a -> H a

-- | Handler for non-deterministic computations
handle_Nondet :: Free Nondet a -> [a]
handle_Nondet = fold alg_Nondet gen_Nondet

-- The variables are handled by the gen_Nondet generator which interprets
-- variables
gen_Nondet :: a -> [a]
gen_Nondet x = [x]

-- The Nondet nodes are handled by the alg_Nondet algebra that
-- interprets terms constructed by `Or` operations:
alg_Nondet :: Nondet [a] -> [a]
alg_Nondet (Or l1 l2) = l1 ++ l2

-- | Coproduct
data (+) f g a where
   Inl :: f a -> (f + g) a
   Inr :: g a -> (f + g) a

instance (Functor f, Functor g) => Functor (f + g) where
   fmap f (Inl s) = Inl (fmap f s)
   fmap f (Inr s) = Inr (fmap f s)

-- | Compositional handler
--   handle :: Free (F + g) a -> H1 (Free g (G1 a))

-- | Algebra combinator
(∇) :: (f b -> b) -> (g b -> b) -> ((f + g) b -> b)
(∇) alg_f alg_g (Inl s) = alg_f s
(∇) alg_f alg_g (Inr s) = alg_g s

-- | Compositional handler for non-deterministic computations
--   handle :: ∀ g a . Free (F + g) a -> H1 (Free g (G1 a))
--     where F = Nondet, G1 = [ ] and implicitly H1 = Id.
handle_Nondet' :: Functor g => Free (Nondet + g) a -> Free g [a]
handle_Nondet' = fold (alg_Nondet' ∇ con_Nondet') gen_Nondet'

-- The variables are handled with the free monadified version of the
-- previous gen_Nondet:
gen_Nondet' :: Functor g => a -> Free g [a]
gen_Nondet' x = Var [x]

-- The Nondet nodes are handled by the free monadified version of the
-- previous alg_Nondet algebra,
alg_Nondet' :: Functor g => Nondet (Free g [a]) -> Free g [a]
alg_Nondet' (Or ml1 ml2) =
   do l1 <- ml1
      l2 <- ml2
      Var (l1 ++ l2)

-- The g nodes are handled by a Con algebra (which essentially
-- leaves them untouched).
con_Nondet' :: Functor g => g (Free g a) -> Free g a
con_Nondet' = Con

-- | State
data State s k where
   Put :: s  -> k  -> State s k
   Get :: (s -> k) -> State s k

instance Functor (State s) where
   fmap f (Put s k) = Put s (f k)
   fmap f (Get k)   = Get (f . k)

-- | Compositional handler for stateful computations
--   handle :: ∀ g a . Free (F + g) a -> H1 (Free g (G1 a))
--     where F is State s, H1 is (s -> -), and implicitly G1 is Id
handle_State :: Functor g => Free (State s + g) a -> (s -> Free g a)
handle_State = fold (alg_State ∇ con_State) gen_State

-- The variables are handled with gen_State
gen_State :: Functor g => a -> (s -> Free g a)
gen_State x = (\s -> Var x)

-- The State nodes are handled by the alg_State algebra.
alg_State :: Functor g => State s (s -> Free g a) -> (s -> Free g a)
alg_State (Put s' k) = \s -> k s'
alg_State (Get k)    = \s -> k s s

-- The g nodes are handled by the con_State algebra.
con_State :: Functor g => g (s -> Free g a) -> (s -> Free g a)
con_State op = \s -> Con ( fmap (\(m :: s -> Free g a)
                                    -> m s) op )



main :: IO ()
main = return ()