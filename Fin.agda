{-# OPTIONS --without-K #-}
module Fin where

open import Base


Fin : Nat → Set
Fin zero    = ⊥
Fin (suc n) = ⊤ ⊎ Fin n
