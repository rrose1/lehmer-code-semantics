{-# OPTIONS --without-K #-}
module LehmerCodes where

open import Base
open import BoundedLinear
open import Fin


data LehmerCode : Nat → Set where
  [] : LehmerCode 0
  ins : {n : Nat} → BNat (suc n) → (p : LehmerCode n) → LehmerCode (suc n)

ins-eqv : {n : Nat} → LehmerCode (suc n) ≃ BNat (suc n) × LehmerCode n
f ins-eqv (ins b p) = b , p
g ins-eqv (b , p)   = ins b p
η ins-eqv (ins b p) = refl
h ins-eqv           = g ins-eqv
ε ins-eqv (b , p)   = refl

----------

sem : {n : Nat} → LehmerCode n ≃ (BNat n ≃ BNat n)
f (sem {zero}) [] = ide (BNat zero)
g (sem {zero}) e  = []
η (sem {zero}) [] = refl
h (sem {zero}) = g (sem {zero})
ε (sem {zero}) e = biinv-eq (funext (λ {(_ , ())}))

sem {suc n} =
  !e  bnat-eqv ∘e
  ide (BNat (suc n)) ×e sem {n} ∘e
  ins-eqv


fin-bnat-eqv : {n : Nat} → Fin n ≃ BNat n
f (fin-bnat-eqv {zero}) ()
g (fin-bnat-eqv {zero}) (_ , ())
η (fin-bnat-eqv {zero}) ()
h (fin-bnat-eqv {zero}) = g (fin-bnat-eqv {zero})
ε (fin-bnat-eqv {zero}) (_ , ())
fin-bnat-eqv {suc n} = bnat-suc-eqv ∘e ide ⊤ ⊎e fin-bnat-eqv {n}


sem-2 : {n : Nat} → LehmerCode n ≃ (Fin n ≃ Fin n)
sem-2 = ∘e-bicomp-eqv fin-bnat-eqv (!e fin-bnat-eqv) ∘e sem
