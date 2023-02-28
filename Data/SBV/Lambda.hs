-----------------------------------------------------------------------------
-- |
-- Module    : Data.SBV.Lambda
-- Copyright : (c) Levent Erkok
-- License   : BSD3
-- Maintainer: erkokl@gmail.com
-- Stability : experimental
--
-- A simple expression language over closed terms, used in creating
-- lambda-expressions for (limited) higher-order function support.
-----------------------------------------------------------------------------

{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE NamedFieldPuns        #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

{-# OPTIONS_GHC -Wall -Werror #-}

module Data.SBV.Lambda (
          lambda
        ) where

import Data.SBV.Core.Data
import Data.SBV.Core.Model
import Data.SBV.Core.Symbolic

import Data.Proxy

-- | Values that we can turn into a lambda abstraction
class Lambda a where
   -- | Turn a symbolic computation to an encapsulated lambda
   -- >>> lambda (2 :: SInteger)
   -- WHAT
   -- >>> lambda (\x -> x+1::SInteger)
   -- WHAT
   -- >>> lambda (\x y -> x+y*2 :: SInteger)
   -- WHAT
   -- >>> lambda (\x (y, z) -> x+y*2+z :: SInteger)
   -- WHAT
   -- >>> lambda (\x (y, z) k -> x+y*2+z + k :: SInteger)
   -- WHAT
  lambda :: a -> IO String

-- | Turn a closed symbolic computation to a lambda
instance Lambda (Symbolic (SBV a)) where
  lambda cmp = do ((), res) <- runSymbolic Lambda (cmp >>= output >> return ())
                  pure $ show res

-- | Base case, simple values
instance Lambda (SBV a) where
  lambda = lambda . (pure :: SBV a -> Symbolic (SBV a))

-- | Functions
instance (SymVal a, Lambda r) => Lambda (SBV a -> r) where
  lambda fn = do arg <- mkSymVal (NonQueryVar Nothing) Nothing
                 lambda $ fn arg

-- | Functions of 2-tuple argument
instance (SymVal a, SymVal b, Lambda r) => Lambda ((SBV a, SBV b) -> r) where
  lambda fn = lambda $ \a b -> fn (a, b)

-- | Functions of 3-tuple arguments
instance (SymVal a, SymVal b, SymVal c, Lambda r) => Lambda ((SBV a, SBV b, SBV c) -> r) where
  lambda fn = lambda $ \a b c -> fn (a, b, c)

-- | Functions of 4-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, Lambda r) => Lambda ((SBV a, SBV b, SBV c, SBV d) -> r) where
  lambda fn = lambda $ \a b c d-> fn (a, b, c, d)

-- | Functions of 5-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, Lambda r) => Lambda ((SBV a, SBV b, SBV c, SBV d, SBV e) -> r) where
  lambda fn = lambda $ \a b c d e -> fn (a, b, c, d, e)

-- | Functions of 6-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, Lambda r) => Lambda ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f) -> r) where
  lambda fn = lambda $ \a b c d e f -> fn (a, b, c, d, e, f)

-- | Functions of 7-tuple arguments
instance (SymVal a, SymVal b, SymVal c, SymVal d, SymVal e, SymVal f, SymVal g, Lambda r) => Lambda ((SBV a, SBV b, SBV c, SBV d, SBV e, SBV f, SBV g) -> r) where
  lambda fn = lambda $ \a b c d e f g -> fn (a, b, c, d, e, f, g)
