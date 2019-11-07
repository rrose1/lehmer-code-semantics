{-# OPTIONS --without-K #-}
module BoundedLinear where

open import Base


infix 4 _<_ _>_
data _<_ : Nat → Nat → Set where
  zero-lt : {n : Nat} → zero < suc n
  suc-lt : {m n : Nat} → m < n → suc m < suc n

pred : Nat → Nat
pred zero    = zero
pred (suc n) = n

suc-pred : {m n : Nat} → m < n → suc (pred n) ≡ n
suc-pred zero-lt = refl
suc-pred (suc-lt r) = refl

lt-suc-1 : {n : Nat} → n < suc n
lt-suc-1 {zero} = zero-lt
lt-suc-1 {suc n} = suc-lt lt-suc-1

lt-suc-2 : {m n : Nat} → m < n → m < suc n
lt-suc-2 zero-lt = zero-lt
lt-suc-2 (suc-lt r) = suc-lt (lt-suc-2 r)

lt-trans : {k m n : Nat} → k < m → m < n → k < n
lt-trans zero-lt (suc-lt r2) = zero-lt
lt-trans (suc-lt r1) (suc-lt r2) = suc-lt (lt-trans r1 r2)

strict : {m n : Nat} → m < n → m ≡ n → ⊥
strict zero-lt ()
strict (suc-lt r) refl = strict r refl

lt-sup : {k m n : Nat} → k < m → m < suc n → k < n
lt-sup {0}     {suc m} {suc n} zero-lt     (suc-lt r2) = zero-lt
lt-sup {suc k} {suc m} {suc n} (suc-lt r1) (suc-lt r2) = suc-lt (lt-sup r1 r2)

lt-pred : {k m n : Nat} → k < m → m < suc n → pred m < n
lt-pred zero-lt (suc-lt r2) = r2
lt-pred (suc-lt r1) (suc-lt r2) = r2

discrete-1 : {m n : Nat} → m < n → n < suc m → ⊥
discrete-1 (suc-lt r1) (suc-lt r2) = discrete-1 r1 r2

discrete-2 : {m n : Nat} → pred m < n → n < m → ⊥
discrete-2 (suc-lt r1) (suc-lt r2) = discrete-2 r1 r2

tpt-lt : {m1 m2 : Nat} → m1 ≡ m2 →
         {n1 n2 : Nat} → n1 ≡ n2 →
         m1 < n1 → m2 < n2
tpt-lt refl refl w = w

lt-is-prop : {m n : Nat} → is-prop (m < n)
lt-is-prop zero-lt zero-lt = refl
lt-is-prop (suc-lt r1) (suc-lt r2) = ap suc-lt (lt-is-prop r1 r2)

_>_ : Nat → Nat → Set
m > n = n < m

BNat : (n : Nat) → Set
BNat n = Σ Nat (λ i → i < n)

bnat-eq : {n : Nat} → {k m : BNat n} → fst k ≡ fst m → k ≡ m
bnat-eq {k = k , v} {_ , w} refl = ap (_,_ k) (lt-is-prop v w)

module _ {n : Nat} (e : BNat n ≃ BNat n) where
  ε-bnat-aut : {m : Nat} → {u : m < n} →
               (v : fst (g e (m , u)) < n) → (w : m < n) →
               f e (fst (g e (m , u)) , v) ≡ (m , w)
  ε-bnat-aut {m} {u} _ _ = ap (f e) (bnat-eq refl) ◾ ε' e (m , u) ◾ bnat-eq refl

  η-bnat-aut : {m : Nat} → {u : m < n} →
               (v : fst (f e (m , u)) < n) → (w : m < n) →
               g e (fst (f e (m , u)) , v) ≡ (m , w)
  η-bnat-aut {m} {u} _ _ = ap (g e) (bnat-eq refl) ◾ η e (m , u) ◾ bnat-eq refl


data BLinear {n : Nat} : BNat n → BNat n → Set where
  lt : {k m : BNat n} → (w : fst k < fst m) → BLinear k m
  eq : {k m : BNat n} → (w : fst k ≡ fst m) → BLinear k m
  gt : {k m : BNat n} → (w : fst k > fst m) → BLinear k m

blinear-suc : {n : Nat} →
              {k m : BNat n} → BLinear k m →
              BLinear (suc (fst k) , suc-lt (snd k)) (suc (fst m) , suc-lt (snd m))
blinear-suc (lt w) = lt (suc-lt w)
blinear-suc (eq w) = eq (ap suc w)
blinear-suc (gt w) = gt (suc-lt w)

blinear : {n : Nat} → (k m : BNat n) → BLinear k m
blinear {n}     (_ , zero-lt)   (_ , zero-lt)   = eq refl
blinear {n}     (_ , zero-lt)   (_ , suc-lt w) = lt zero-lt
blinear {n}     (_ , suc-lt v) (_ , zero-lt)   = gt zero-lt
blinear {suc n} (_ , suc-lt v) (_ , suc-lt w) = blinear-suc (blinear (_ , v) (_ , w))

blinear-β-lt : {n : Nat} → {k m : BNat n} → (r : fst k < fst m) →
               blinear k m ≡ lt r
blinear-β-lt {suc _} {_ , zero-lt}  {_ , suc-lt _} zero-lt    = refl
blinear-β-lt {suc _} {_ , suc-lt _} {_ , suc-lt _} (suc-lt r) =
             ap blinear-suc (blinear-β-lt r)

blinear-β-eq : {n : Nat} → {k m : BNat n} → (r : fst k ≡ fst m) →
               blinear k m ≡ eq r
blinear-β-eq {_}     {_ , zero-lt}  {_ , zero-lt}  refl = refl
blinear-β-eq {suc _} {_ , suc-lt v} {_ , suc-lt w} refl =
             ap blinear-suc (blinear-β-eq {_} {_ , v} {_ , w} refl)

blinear-β-gt : {n : Nat} → {k m : BNat n} → (r : fst k > fst m) →
               blinear k m ≡ gt r
blinear-β-gt {suc _} {_ , suc-lt _} {_ , zero-lt}  zero-lt    = refl
blinear-β-gt {suc _} {_ , suc-lt _} {_ , suc-lt _} (suc-lt r) =
             ap blinear-suc (blinear-β-gt r)


{- TODO : remove unnamed where modules -}
bnat-eqv : {n : Nat} →
           (BNat (suc n) ≃ BNat (suc n)) ≃ BNat (suc n) × (BNat n ≃ BNat n)
f (bnat-eqv {n}) e =
  f e (n , lt-suc-1) ,
  aux1 (blinear (f e (n , lt-suc-1)) (n , lt-suc-1))
  module f-bnat-eqv where
  aux1 : BLinear (f e (n , lt-suc-1)) (n , lt-suc-1) → (BNat n ≃ BNat n)
  
  f (aux1 (lt w1)) (k , v) = aux2 (blinear _ _)
    module f-aux1-lt where
    aux2 : BLinear (f e (k , lt-suc-2 v)) (f e (n , lt-suc-1)) → BNat n
    aux2 (lt w2) = fst (f e (k , lt-suc-2 v)) , lt-trans w2 w1
    aux2 (eq w2) =
      rec⊥ (strict v (ap fst (! (η e _) ◾ ap (g e) (bnat-eq w2) ◾ η e _)))
    aux2 (gt w2) = pred (fst (f e (k , lt-suc-2 v))) ,
                   lt-pred w2 (snd (f e (k , lt-suc-2 v)))

  g (aux1 (lt w1)) (k , v) = aux2 (blinear _ _)
    module g-aux1-lt where
    aux2 : BLinear (k , lt-suc-2 v) (f e (n , lt-suc-1)) → BNat n
    aux2 (lt w2) = fst (g e (k , lt-suc-2 v)) , aux3 (blinear _ _)
      module aux2-lt where
      aux3 : BLinear (g e (k , lt-suc-2 v)) (n , lt-suc-1) →
             fst (g e (k , lt-suc-2 v)) < n
      aux3 (lt w3) = w3
      aux3 (eq w3) =
        rec⊥ (strict w2
          (ap fst (! (ε-bnat-aut e (snd (g e (k , lt-suc-2 v))) (lt-suc-2 v)) ◾
                   ap (f e) (bnat-eq w3))))
      aux3 (gt w3) = rec⊥ (discrete-1 w3 (snd (g e (k , lt-suc-2 v))))
      
    aux2 (eq w2) = fst (g e (suc k , suc-lt v)) , aux3 (blinear _ _)
      module aux2-eq where
      aux3 : BLinear (g e (suc k , suc-lt v)) (n , lt-suc-1) →
             fst (g e (suc k , suc-lt v)) < n
      aux3 (lt w3) = w3
      aux3 (eq w3) =
        rec⊥ (strict lt-suc-1
          (ap fst
              (! (ε-bnat-aut e (snd (g e (k , lt-suc-2 v))) (lt-suc-2 v)) ◾
               ap (f e) (ap (g e) (bnat-eq w2) ◾
               η-bnat-aut e (snd (f e (n , lt-suc-1))) lt-suc-1 ◾
               ! (bnat-eq w3)) ◾
               ε-bnat-aut e (snd (g e (suc k , suc-lt v))) (suc-lt v))))
      aux3 (gt w3) = rec⊥ (discrete-1 w3 (snd (g e (suc k , suc-lt v))))
      
    aux2 (gt w2) = fst (g e (suc k , suc-lt v)) , aux3 (blinear _ _)
      module aux2-gt where
      aux3 : BLinear (g e (suc k , suc-lt v)) (n , lt-suc-1) →
             fst (g e (suc k , suc-lt v)) < n
      aux3 (lt w3) = w3
      aux3 (eq w3) =
        rec⊥ (strict (lt-suc-2 w2)
          (ap fst (! (ap (f e) (bnat-eq w3)) ◾
                   ε-bnat-aut e (snd (g e (suc k , suc-lt v))) (suc-lt v))))
      aux3 (gt w3) = rec⊥ (discrete-1 w3 (snd (g e (suc k , suc-lt v))))

  η (aux1 (lt w1)) (k , v) = aux2 (blinear _ _)
    module η-aux2-lt where
    aux2 : (a1 : BLinear (f e (k , lt-suc-2 v)) (f e (n , lt-suc-1))) →
           g-aux1-lt.aux2 w1
             (fst (f-aux1-lt.aux2 w1 k v a1))
             (snd (f-aux1-lt.aux2 w1 k v a1))
             (blinear (fst (f-aux1-lt.aux2 w1 k v a1) ,
                       lt-suc-2 (snd (f-aux1-lt.aux2 w1 k v a1)))
                      (f e (n , lt-suc-1))) ≡ (k , v)
    aux2 (lt w2) = aux3 (blinear _ _)
      where -- named module not allowed
      aux3 : (a2 : BLinear (fst (f-aux1-lt.aux2 w1 k v (lt w2)) ,
                            lt-suc-2 (snd (f-aux1-lt.aux2 w1 k v (lt w2))))
                           (f e (n , lt-suc-1))) →
             g-aux1-lt.aux2 w1
               (fst (f-aux1-lt.aux2 w1 k v (lt w2)))
               (snd (f-aux1-lt.aux2 w1 k v (lt w2))) a2 ≡ (k , v)
      aux3 (lt w3) = bnat-eq (ap fst (η-bnat-aut e _ (lt-suc-2 v)))        
      aux3 (eq w3) =
        rec⊥ (strict v (ap fst (! (η e _) ◾ ap (g e) (bnat-eq w3) ◾ η e _)))
      aux3 (gt w3) = rec⊥ (strict (lt-trans w3 w2) refl)
        
    aux2 (eq w2) =
      rec⊥ (strict v (ap fst (! (η e _) ◾ ap (g e) (bnat-eq w2) ◾ η e _)))
    
    aux2 (gt w2) = aux3 (blinear _ _)
      where -- named module not allowed
      aux3 : (a3 : BLinear (fst (f-aux1-lt.aux2 w1 k v (gt w2)) ,
                             lt-suc-2 (snd (f-aux1-lt.aux2 w1 k v (gt w2))))
                           (f e (n , lt-suc-1))) →
             g-aux1-lt.aux2 w1
               (fst (f-aux1-lt.aux2 w1 k v (gt w2)))
               (snd (f-aux1-lt.aux2 w1 k v (gt w2))) a3 ≡ (k , v)
      aux3 (lt w3) = rec⊥ (discrete-2 w3 w2)
      aux3 (eq w3) = bnat-eq (ap fst (ap (g e) (bnat-eq (suc-pred w2)) ◾ η e _))
      aux3 (gt w3) = bnat-eq (ap fst (ap (g e) (bnat-eq (suc-pred w2)) ◾ η e _))
      
  h (aux1 (lt w1)) = g (aux1 (lt w1))
  ε (aux1 (lt w1)) (k , v) = aux2 (blinear _ _)
    module ε-aux1-lt where
    aux2 : (a2 : BLinear (k , lt-suc-2 v) (f e (n , lt-suc-1))) →
           f-aux1-lt.aux2 w1
             (fst (g-aux1-lt.aux2 w1 k v a2))
             (snd (g-aux1-lt.aux2 w1 k v a2))
             (blinear (f e (fst (g-aux1-lt.aux2 w1 k v a2) ,
                       lt-suc-2 (snd (g-aux1-lt.aux2 w1 k v a2))))
                      (f e (n , lt-suc-1))) ≡ (k , v)
    aux2 (lt w2) = aux3 (blinear _ _)
      where -- named module not allowed
      aux3 : (a3 : BLinear (g e (k , lt-suc-2 v)) (n , lt-suc-1)) →
             f-aux1-lt.aux2 w1
               (fst (g e (k , lt-suc-2 v)))
               (g-aux1-lt.aux2-lt.aux3 w1 k v w2 a3)
               (blinear (f e (fst (g e (k , lt-suc-2 v)) ,
                         lt-suc-2 (g-aux1-lt.aux2-lt.aux3 w1 k v w2 a3)))
                        (f e (n , lt-suc-1))) ≡ (k , v)
      aux3 (lt w3) = aux4 (blinear _ _)
        where -- named module not allowed
        aux4 : (a4 : BLinear (f e (fst (g e (k , lt-suc-2 v)) , lt-suc-2 w3))
                             (f e (n , lt-suc-1))) →
               f-aux1-lt.aux2 w1 (fst (g e (k , lt-suc-2 v))) w3 a4 ≡ (k , v)
        aux4 (lt w4) = bnat-eq (ap fst (ε-bnat-aut e (lt-suc-2 w3) (lt-suc-2 v)))
        aux4 (eq w4) =
          rec⊥ (strict w3
            (ap fst
                (! (η e (fst (g e (k , lt-suc-2 v)) , lt-suc-2 w3)) ◾
                 ap (g e) (bnat-eq w4) ◾
                 η e (n , lt-suc-1))))
        aux4 (gt w4) =
          rec⊥ (strict (lt-trans w2 w4)
                       (! (ap fst (ε-bnat-aut e (lt-suc-2 w3) (lt-suc-2 v)))))
      aux3 (eq w3) =
        rec⊥ (strict w2
          (ap fst (! (ε-bnat-aut e (snd (g e (k , lt-suc-2 v))) (lt-suc-2 v)) ◾
                   ap (f e) (bnat-eq w3))))
      aux3 (gt w3) = rec⊥ (discrete-1 w3 (snd (g e (k , lt-suc-2 v))))
      
    aux2 (eq w2) = aux3 (blinear _ _)
      where -- named module not allowed
      aux3 : (a3 : BLinear (g e (suc k , suc-lt v)) (n , lt-suc-1)) →
             f-aux1-lt.aux2 w1
               (fst (g e (suc k , suc-lt v)))
               (g-aux1-lt.aux2-eq.aux3 w1 k v w2 a3)
               (blinear (f e (fst (g e (suc k , suc-lt v)) ,
                                   lt-suc-2 (g-aux1-lt.aux2-eq.aux3 w1 k v w2 a3)))
                        (f e (n , lt-suc-1))) ≡ (k , v)
      aux3 (lt w3) = aux4 (blinear _ _)
        where -- named module not allowed
        aux4 : (a4 : BLinear (f e (fst (g e (suc k , suc-lt v)) , lt-suc-2 w3))
                             (f e (n , lt-suc-1))) →
               f-aux1-lt.aux2 w1 (fst (g e (suc k , suc-lt v))) w3 a4 ≡ (k , v)
        aux4 (lt w4) =
          rec⊥ (strict (lt-suc-2
            (tpt-lt (ap fst (ε-bnat-aut e _ (suc-lt v))) (! w2) w4)) refl)
        aux4 (eq w4) =
          rec⊥ (strict w3
            (ap fst (! (η e (fst (g e (suc k , suc-lt v)) , lt-suc-2 w3)) ◾
                     ap (g e) (bnat-eq w4) ◾
                     η e (n , lt-suc-1))))
        aux4 (gt w4) =
          bnat-eq (ap pred (ap fst (ε-bnat-aut e (lt-suc-2 w3) (suc-lt v))))
        
      aux3 (eq w3) =
        rec⊥ (strict lt-suc-1
          (ap fst
              (! (ε-bnat-aut e (snd (g e (k , lt-suc-2 v))) (lt-suc-2 v)) ◾
               ap (f e) (ap (g e) (bnat-eq w2) ◾
                         η-bnat-aut e (snd (f e (n , lt-suc-1))) lt-suc-1 ◾
                         ! (bnat-eq w3)) ◾
               ε-bnat-aut e (snd (g e (suc k , suc-lt v))) (suc-lt v))))
      aux3 (gt w3) = rec⊥ (discrete-1 w3 (snd (g e (suc k , suc-lt v))))
      
    aux2 (gt w2) = aux3 (blinear _ _)
      where -- named module not allowed
      aux3 : (a3 : BLinear (g e (suc k , suc-lt v)) (n , lt-suc-1)) →
             f-aux1-lt.aux2 w1
               (fst (g e (suc k , suc-lt v)))
               (g-aux1-lt.aux2-gt.aux3 w1 k v w2 a3)
               (blinear (f e (fst (g e (suc k , suc-lt v)) ,
                         lt-suc-2 (g-aux1-lt.aux2-gt.aux3 w1 k v w2 a3)))
                        (f e (n , lt-suc-1))) ≡ (k , v)
      aux3 (lt w3) = bnat-eq (aux4 (blinear _ _))
        where -- named module not allowed
        aux4 : (a4 : BLinear (f e (fst (g e (suc k , suc-lt v)) , lt-suc-2 w3))
                             (f e (n , lt-suc-1))) →
               fst (f-aux1-lt.aux2 w1 (fst (g e (suc k , suc-lt v))) w3 a4) ≡ k
        aux4 (lt w4) =
          rec⊥ (strict (lt-suc-2 (lt-trans w4 w2))
                        (ap fst (ε-bnat-aut e (lt-suc-2 w3) (suc-lt v)))) 
        aux4 (eq w4) =
          rec⊥ (strict w3
            (ap fst (! (η e (fst (g e (suc k , suc-lt v)) , lt-suc-2 w3)) ◾
                     ap (g e) (bnat-eq w4) ◾
                     η e (n , lt-suc-1))))
        aux4 (gt w4) = ap pred (ap fst (ε-bnat-aut e (lt-suc-2 w3) (suc-lt v)))
        
      aux3 (eq w3) =
        rec⊥ (strict (lt-suc-2 w2)
                      (ap fst (! (ap (f e) (bnat-eq w3)) ◾
                       ε-bnat-aut e (snd (g e (suc k , suc-lt v))) (suc-lt v))))
      aux3 (gt w3) = rec⊥ (discrete-1 w3 (snd (g e (suc k , suc-lt v))))
      
  -----
  f (aux1 (eq w1)) (k , v) =
    fst (f e (k , lt-suc-2 v)) ,
    aux2 (blinear _ _)
    module f-aux1-eq where
    aux2 : BLinear (f e (k , lt-suc-2 v)) (n , lt-suc-1) →
           fst (f e (k , lt-suc-2 v)) < n
    aux2 (lt w2) = w2
    aux2 (eq w2) =
      rec⊥ (strict v (! (ap fst (! ((η e) (n , lt-suc-1)) ◾
                      ap (g e) (bnat-eq (w1 ◾ ! w2)) ◾
                      (η e) (k , lt-suc-2 v)))))
    aux2 (gt w2) =
      rec⊥ (discrete-1 w2 (snd (f e (k , lt-suc-2 v))))

  g (aux1 (eq w1)) (k , v) =
    fst (g e (k , lt-suc-2 v)) ,
    aux2 (blinear (g e (k , lt-suc-2 v)) (n , lt-suc-1))
    module g-aux1-eq where
    aux2 : BLinear (g e (k , lt-suc-2 v)) (n , lt-suc-1) →
           fst (g e (k , lt-suc-2 v)) < n
    aux2 (lt w2) = w2
    aux2 (eq w2) =
      rec⊥ (strict v
        (! (ap fst (ε-bnat-aut e (snd (g e (k , lt-suc-2 v))) (lt-suc-2 v))) ◾
         ap (λ m → fst (f e m)) (bnat-eq w2) ◾
         w1))
    aux2 (gt w2) = rec⊥ (discrete-1 w2 (snd (g e (k , lt-suc-2 v))))

  η (aux1 (eq w)) (k , v) = bnat-eq (ap fst (η-bnat-aut e _ (lt-suc-2 v)))
  h (aux1 (eq w)) = g (aux1 (eq w))
  ε (aux1 (eq w)) (k , v) = bnat-eq (ap fst (ε-bnat-aut e _ (lt-suc-2 v)))

  -----
  aux1 (gt w1) =
    rec⊥ (discrete-1 w1 (snd (f e (n , lt-suc-1))))
  
-----
g (bnat-eqv {n}) ((k , v) , e) = aux1 (blinear _ _)
  module g-bnat-eqv where
  aux1 : BLinear (k , v) (n , lt-suc-1) → BNat (suc n) ≃ BNat (suc n)
  f (aux1 (lt w1)) (j , u) = aux2 (blinear _ _)
    module f-aux1-lt where
    aux3 : (w2 : j < n) → BLinear (f e (j , w2)) (k , w1) → BNat (suc n)
    aux3 w2 (lt w3) = fst (f e (j , w2)) , lt-suc-2 (snd (f e (j , w2)))
    aux3 w2 (eq w3) = suc (fst (f e (j , w2))) , suc-lt (snd (f e (j , w2)))
    aux3 w2 (gt w3) = suc (fst (f e (j , w2))) , suc-lt (snd (f e (j , w2)))

    aux2 : BLinear (j , u) (n , lt-suc-1) → BNat (suc n)
    aux2 (lt w2) = aux3 w2 (blinear _ _)
    aux2 (eq w2) = k , v
    aux2 (gt w2) = rec⊥ (discrete-1 u (suc-lt w2))
    
  g (aux1 (lt w1)) (j , u) = aux2 (blinear _ _)
    module g-aux1-lt where
    aux2 : BLinear (j , u) (k , v) → BNat (suc n)
    aux2 (lt w2) = fst (g e (j , lt-sup w2 v)) ,
                   lt-suc-2 (snd (g e (j , lt-sup w2 v)))
    aux2 (eq w2) = n , lt-suc-1
    aux2 (gt w2) = fst (g e (pred j , lt-pred w2 u)) ,
                   lt-suc-2 (snd (g e (pred j , lt-pred w2 u)))
  
  η (aux1 (lt w1)) (j , u) = bnat-eq (aux2 (blinear _ _))
    module η-aux1-lt where
    aux2 : (a2 : BLinear (f-aux1-lt.aux2 w1 j u (blinear (j , u) (n , lt-suc-1)))
                         (k , v)) →
           fst (g-aux1-lt.aux2 w1
             (fst (f-aux1-lt.aux2 w1 j u (blinear (j , u) (n , lt-suc-1))))
             (snd (f-aux1-lt.aux2 w1 j u (blinear (j , u) (n , lt-suc-1)))) a2) ≡
           j
    aux2 (lt w2) = aux4 (blinear _ _) w2
      module aux2-lt where
      aux3 : (w4 : j < n) → (a3 : BLinear (f e (j , w4)) (k , w1)) →
             (w2 : fst (f-aux1-lt.aux3 w1 j u w4 a3) < k) →
             fst (g e (fst (f-aux1-lt.aux3 w1 j u w4 a3) , lt-sup w2 v)) ≡ j
      aux3 w4 (lt w3) w2 = ap fst (η-bnat-aut e (lt-sup w2 v) w4)
      aux3 w4 (eq w3) w2 = rec⊥ (strict (lt-suc-2 w2) (ap suc w3))
      aux3 w4 (gt w3) w2 = rec⊥ (strict (lt-trans (lt-suc-2 w3) w2) refl)

      aux4 : (a4 : BLinear (j , u) (n , lt-suc-1)) →
             (w2 : fst (f-aux1-lt.aux2 w1 j u a4) < k) →
             fst (g e (fst (f-aux1-lt.aux2 w1 j u a4) , lt-sup w2 v)) ≡ j
      aux4 (lt w4) w2 = aux3 w4 (blinear _ _) w2
      aux4 (eq w4) w2 = rec⊥ (strict w2 refl)
      aux4 (gt w4) w2 = rec⊥ (discrete-1 u (suc-lt w4))
      
    aux2 (eq w2) = aux4 (blinear _ _) w2
      module aux2-eq where
      aux3 : (w4 : j < n) → (a3 : BLinear (f e (j , w4)) (k , w1)) →
             (w2 : fst (f-aux1-lt.aux3 w1 j u w4 a3) ≡ k) → n ≡ j
      aux3 w4 (lt w3) w2 = rec⊥ (strict w3 w2)
      aux3 w4 (eq w3) w2 = rec⊥ (strict lt-suc-1 (w3 ◾ ! w2))
      aux3 w4 (gt w3) w2 = rec⊥ (strict (lt-suc-2 w3) (! w2))

      aux4 : (a4 : BLinear (j , u) (n , lt-suc-1)) →
             (w2 : fst (f-aux1-lt.aux2 w1 j u a4) ≡ k) → n ≡ j
      aux4 (lt w4) w2 = aux3 w4 (blinear _ _) w2
      aux4 (eq w4) _  = ! w4
      aux4 (gt w4)    = rec⊥ (discrete-1 u (suc-lt w4))

    aux2 (gt w2) = aux4 (blinear _ _) w2
      module aux2-gt where
      aux3 : (w4 : j < n) → (a3 : BLinear (f e (j , w4)) (k , w1)) →
             (w2 : fst (f-aux1-lt.aux3 w1 j u w4 a3) > k) →
             fst (g e (pred (fst (f-aux1-lt.aux3 w1 j u w4 a3)) ,
                       lt-pred w2 (snd (f-aux1-lt.aux3 w1 j u w4 a3)))) ≡ j
      aux3 w4 (lt w3) w2 = rec⊥ (strict (lt-trans w3 w2) refl)
      aux3 w4 (eq w3) w2 =
        ap fst (η-bnat-aut e (lt-pred w2 _) w4)
      aux3 w4 (gt w3) w2 =
        ap fst (η-bnat-aut e (lt-pred w2 _) w4)
      
      aux4 : (a4 : BLinear (j , u) (n , lt-suc-1)) →
             (w2 : fst (f-aux1-lt.aux2 w1 j u a4) > k) →
             fst (g e (pred (fst (f-aux1-lt.aux2 w1 j u a4)) ,
                  lt-pred w2 (snd (f-aux1-lt.aux2 w1 j u a4)))) ≡ j
      aux4 (lt w4) w2 = aux3 w4 (blinear _ _) w2
      aux4 (eq w4) w2 = rec⊥ (strict w2 refl)
      aux4 (gt w4) w2 = rec⊥ (discrete-1 u (suc-lt w4))
      
  h (aux1 (lt w1)) = g (aux1 (lt w1))
  
  ε (aux1 (lt w1)) (j , u) = bnat-eq (aux5 (blinear _ _))
    module ε-aux1-lt where
    aux2 : (w5 : j < k) →
           (a2 : BLinear (fst (g e (j , lt-sup w5 v)) ,
                          lt-suc-2 (snd (g e (j , lt-sup w5 v))))
                         (n , lt-suc-1)) →
           fst (f-aux1-lt.aux2 w1
                 (fst (g e (j , lt-sup w5 v)))
                 (lt-suc-2 (snd (g e (j , lt-sup w5 v)))) a2) ≡ j
    aux2 w5 (lt w2) =
      ap (λ b → fst (f-aux1-lt.aux3 w1
                       (fst (g e (j , lt-sup w5 v)))
                       (lt-suc-2 (snd (g e (j , lt-sup w5 v)))) w2 b))
         (blinear-β-lt (tpt-lt
           (! (ap fst (ε-bnat-aut e w2 (lt-sup w5 v)))) refl w5)) ◾
            ap fst (ε-bnat-aut e w2 (lt-sup w5 v))
    aux2 w5 (eq w2) =
      rec⊥ (strict (tpt-lt w2 refl (snd (g e (j , lt-sup w5 v)))) refl)
    aux2 w5 (gt w2) =
      rec⊥ (discrete-1 (lt-suc-2 (snd (g e (j , lt-sup w5 v)))) (suc-lt w2))


    aux3 : (w5 : k < j) → (w4 : fst (g e (pred j , lt-pred w5 u)) < n) →
           (a3 : BLinear (f e (fst (g e (pred j , lt-pred w5 u)) , w4)) (k , w1)) →
           fst (f-aux1-lt.aux3 w1
                  (fst (g e (pred j , lt-pred w5 u)))
                  (lt-suc-2 (snd (g e (pred j , lt-pred w5 u)))) w4 a3) ≡ j
    aux3 w5 w4 (lt w3) =
      rec⊥ (discrete-2 (tpt-lt (ap fst (ε-bnat-aut e w4 (lt-pred w5 u))) refl w3) w5)
    aux3 w5 w4 (eq w3) =
      ap suc (ap fst (ε-bnat-aut e _ (lt-pred w5 u))) ◾ suc-pred w5
    aux3 w5 w4 (gt w3) =
      ap suc (ap fst (ε-bnat-aut e _ (lt-pred w5 u))) ◾ suc-pred w5

    aux4 : (w5 : k < j) →
           (a4 : BLinear (fst (g e (pred j , lt-pred w5 u)) ,
                          lt-suc-2 (snd (g e (pred j , lt-pred w5 u))))
                         (n , lt-suc-1)) →
           fst (f-aux1-lt.aux2 w1
                  (fst (g e (pred j , lt-pred w5 u)))
                  (lt-suc-2 (snd (g e (pred j , lt-pred w5 u)))) a4) ≡
           j
    aux4 w5 (lt w4) = aux3 w5 w4 (blinear _ _)
    aux4 w5 (eq w4) = rec⊥ (strict (snd (g e (pred j , lt-pred w5 u))) w4)
    aux4 w5 (gt w4) =
      rec⊥ (discrete-1 (lt-suc-2 (snd (g e (pred j , lt-pred w5 u)))) (suc-lt w4))

    aux5 : (a5 : BLinear (j , u) (k , v)) →
           fst (f-aux1-lt.aux2 w1
                  (fst (g-aux1-lt.aux2 w1 j u a5))
                  (snd (g-aux1-lt.aux2 w1 j u a5))
                  (blinear (g-aux1-lt.aux2 w1 j u a5)
                           (n , lt-suc-1))) ≡
           j
    aux5 (lt w5) = aux2 w5 (blinear _ _)
    aux5 (eq w5) =
      ap (λ b → fst (f-aux1-lt.aux2 w1 n lt-suc-1 b)) (blinear-β-eq refl) ◾ ! w5 
    aux5 (gt w5) = aux4 w5 (blinear _ _)

  -----
  f (aux1 (eq w1)) (j , u) = aux2 (blinear _ _)
    module f-aux1-eq where
    aux2 : BLinear (j , u) (n , lt-suc-1) → BNat (suc n)
    aux2 (lt w2) = fst (f e (j , w2)) , lt-suc-2 (snd (f e (j , w2)))
    aux2 (eq w2) = n , lt-suc-1
    aux2 (gt w2) = rec⊥ (discrete-1 w2 u)

  g (aux1 (eq w1)) (j , u) = aux2 (blinear _ _)
    module g-aux1-eq where
    aux2 : BLinear (j , u) (n , lt-suc-1) → BNat (suc n)
    aux2 (lt w2) = fst (g e (j , w2)) , lt-suc-2 (snd (g e (j , w2)))
    aux2 (eq w2) = n , lt-suc-1
    aux2 (gt w2) = rec⊥ (discrete-1 w2 u)

  η (aux1 (eq w1)) (j , u) = bnat-eq (aux2 (blinear _ _) (blinear _ _))
    module η-aux-eq where
    aux2 : (a2 : BLinear (j , u) (n , lt-suc-1)) →
           (a3 : BLinear (f-aux1-eq.aux2 w1 j u a2) (n , lt-suc-1)) →
           fst (g-aux1-eq.aux2 w1
                  (fst (f-aux1-eq.aux2 w1 j u a2))
                  (snd (f-aux1-eq.aux2 w1 j u a2)) a3) ≡ j
    aux2 (lt w2) (lt w3) = ap fst (η-bnat-aut e w3 w2)
    aux2 (lt w2) (eq w3) = rec⊥ (strict (snd (f e (j , w2))) w3)
    aux2 (lt w2) (gt w3) = rec⊥ (discrete-1 w3 (lt-suc-2 (snd (f e (j , w2)))))
    aux2 (eq w2) (lt w3) = rec⊥ (strict w3 refl)
    aux2 (eq w2) (eq w3) = ! w2
    aux2 (eq w2) (gt w3) = rec⊥ (discrete-1 w3 lt-suc-1)
    aux2 (gt w2) = rec⊥ (discrete-1 w2 u)
  
  h (aux1 (eq w1)) = g (aux1 (eq w1))
  
  ε (aux1 (eq w1)) (j , u) = bnat-eq (aux2 (blinear _ _) (blinear _ _))
    module ε-aux-eq where
    aux2 : (a2 : BLinear (j , u) (n , lt-suc-1)) →
           (a3 : BLinear (g-aux1-eq.aux2 w1 j u a2) (n , lt-suc-1)) →
           fst (f-aux1-eq.aux2 w1
                  (fst (g-aux1-eq.aux2 w1 j u a2))
                  (snd (g-aux1-eq.aux2 w1 j u a2)) a3) ≡ j
    aux2 (lt w2) (lt w3) = ap fst (ε-bnat-aut e w3 w2)
    aux2 (lt w2) (eq w3) = rec⊥ (strict (snd (g e (j , w2))) w3)
    aux2 (lt w2) (gt w3) = rec⊥ (discrete-1 w3 (lt-suc-2 (snd (g e (j , w2)))))
    aux2 (eq w2) (lt w3) = rec⊥ (strict w3 refl)
    aux2 (eq w2) (eq w3) = ! w2
    aux2 (eq w2) (gt w3) = rec⊥ (discrete-1 w3 lt-suc-1)
    aux2 (gt w2) = rec⊥ (discrete-1 w2 u)

  -----
  aux1 (gt w1) = rec⊥ (discrete-1 w1 v)

-----
η (bnat-eqv {n}) e = aux1 (blinear _ _)
  module η-bnat-eqv where
  aux1 : (w1 : BLinear (f e (n , lt-suc-1)) (n , lt-suc-1)) →
         g-bnat-eqv.aux1 (fst (f e (n , lt-suc-1)))
                         (snd (f e (n , lt-suc-1)))
                         (f-bnat-eqv.aux1 e w1) w1 ≡ e
  aux1 (lt w1) = biinv-eq (funext (λ {(k , v) → aux3 k v (blinear _ _)}))
    module aux1-lt where
    aux2 : (k : Nat) → (v : k < suc n) → (w2 : k < n) →
           (a3 : BLinear (f (f-bnat-eqv.aux1 e (lt w1)) (k , w2))
                         (fst (f e (n , lt-suc-1)) , w1)) →
           g-bnat-eqv.f-aux1-lt.aux3
             (fst (f e (n , lt-suc-1)))
             (snd (f e (n , lt-suc-1)))
             (f-bnat-eqv.aux1 e (lt w1)) w1 k v w2 a3 ≡ f e (k , v)
    aux2 k v w2 (lt w3) = bnat-eq (aux4 (blinear _ _) w3)
      module aux2-lt where
      aux4 : (a4 : BLinear (f e (k , lt-suc-2 w2)) (f e (n , lt-suc-1))) →
             (w3 : fst (f-bnat-eqv.f-aux1-lt.aux2 e w1 k w2 a4) <
                   fst (f e (n , lt-suc-1))) →
             fst (f-bnat-eqv.f-aux1-lt.aux2 e w1 k w2 a4) ≡ fst (f e (k , v))
      aux4 (lt w4) _ = ap (λ v → fst (f e (k , v))) (lt-is-prop _ _)
      aux4 (eq w4) _ =
        rec⊥ (strict w2
          (ap fst (! (η e (k , lt-suc-2 w2)) ◾
                   ap (g e) (bnat-eq w4) ◾
                   η e (n , lt-suc-1))))
      aux4 (gt w4) w3 = rec⊥ (discrete-2 w3 w4)
      
    aux2 k v w2 (eq w3) = bnat-eq (aux4 (blinear _ _) w3)
      module aux2-eq where
      aux4 : (a4 : BLinear (f e (k , lt-suc-2 w2)) (f e (n , lt-suc-1))) →
             (w3 : fst (f-bnat-eqv.f-aux1-lt.aux2 e w1 k w2 a4) ≡
                   fst (f e (n , lt-suc-1))) →
             suc (fst (f-bnat-eqv.f-aux1-lt.aux2 e w1 k w2 a4)) ≡ fst (f e (k , v))
      aux4 (lt w4) w3 = rec⊥ (strict w4 w3)
      aux4 (eq w4) w3 =
        rec⊥ (strict w2
          (ap fst (! (η e (k , lt-suc-2 w2)) ◾
                   ap (g e) (bnat-eq w4) ◾
                   η e (n , lt-suc-1))))
                   
      aux4 (gt w4) w3 = suc-pred w4 ◾ ap (λ v → fst (f e (k , v))) (lt-is-prop _ _)
      
    aux2 k v w2 (gt w3) = bnat-eq (aux4 (blinear _ _) w3)
      module aux2-gt where
      aux4 : (a4 : BLinear (f e (k , lt-suc-2 w2)) (f e (n , lt-suc-1))) →
             (w3 : fst (f-bnat-eqv.f-aux1-lt.aux2 e w1 k w2 a4) >
                   fst (f e (n , lt-suc-1))) →
             suc (fst (f-bnat-eqv.f-aux1-lt.aux2 e w1 k w2 a4)) ≡
             fst (f e (k , v))
      aux4 (lt w4) w3 = rec⊥ (strict (lt-trans w3 w4) refl)
      aux4 (eq w4) w3 =
        rec⊥ (strict w2
          (ap fst (! (η e (k , lt-suc-2 w2)) ◾
                   ap (g e) (bnat-eq w4) ◾
                   η e (n , lt-suc-1))))
      aux4 (gt w4) w3 = suc-pred w4 ◾ ap (λ v → fst (f e (k , v))) (lt-is-prop _ _)

    aux3 : (k : Nat) → (v : k < suc (n)) →
           (a2 : BLinear (k , v) (n , lt-suc-1)) →
           g-bnat-eqv.f-aux1-lt.aux2
             (fst (f e (n , lt-suc-1))) (snd (f e (n , lt-suc-1)))
             (f-bnat-eqv.aux1 e (lt w1)) w1 k v a2 ≡
           f e (k , v)
    aux3 k v (lt w2) = aux2 k v w2 (blinear _ _)
    aux3 k v (eq w2) = bnat-eq (ap (λ m → fst (f e m)) (bnat-eq (! w2)))
    aux3 k v (gt w2) = rec⊥ (discrete-1 v (suc-lt w2))
  
  aux1 (eq w1) = biinv-eq (funext (λ {(k , v) → aux2 k v (blinear _ _)}))
    module aux1-eq where
    aux2 : (k : Nat) → (v : k < suc (n)) →
           (w2 : BLinear (k , v) (n , lt-suc-1)) →
           g-bnat-eqv.f-aux1-eq.aux2
             (fst (f e (n , lt-suc-1)))
             (snd (f e (n , lt-suc-1)))
             (f-bnat-eqv.aux1 e (eq w1)) w1 k v w2 ≡ f e (k , v)
    aux2 k v (lt w2) = bnat-eq (ap (λ w → fst (f e (k , w))) (lt-is-prop _ _))
    aux2 k v (eq w2) = bnat-eq (! w1 ◾ ap (λ m → fst (f e m)) (bnat-eq (! w2)))    
    aux2 k v (gt w2) = rec⊥ (discrete-1 w2 v)

  aux1 (gt w1) = rec⊥ (discrete-1 w1 (snd (f e (n , lt-suc-1))))

-----
h (bnat-eqv {n}) = g (bnat-eqv {n})

-----
ε (bnat-eqv {n}) ((k , v) , e) = aux1 (blinear _ _)
  module ε-bnat-eqv where
  aux1 : (a1 : BLinear (k , v) (n , lt-suc-1)) →
         (f (g-bnat-eqv.aux1 k v e a1) (n , lt-suc-1) ,
          f-bnat-eqv.aux1 (g-bnat-eqv.aux1 k v e a1)
            (blinear (f (g-bnat-eqv.aux1 k v e a1) (n , lt-suc-1))
                     (n , lt-suc-1))) ≡ ((k , v) , e)
  aux1 (lt w1) = aux2 _ refl (blinear _ _)
    module aux1-lt where
    aux2 : (a2 : BLinear (n , lt-suc-1) (n , lt-suc-1)) →
           (e2 : blinear (n , lt-suc-1) (n , lt-suc-1) ≡ a2) →
           (a3 : BLinear (f (g-bnat-eqv.aux1 k v e (lt w1)) (n , lt-suc-1))
                         (n , lt-suc-1)) →
           (g-bnat-eqv.f-aux1-lt.aux2 k v e w1 n lt-suc-1 a2 ,
            f-bnat-eqv.aux1 (g-bnat-eqv.aux1 k v e (lt w1)) a3) ≡
           ((k , v) , e)
    aux2 (lt w2) _ _  = rec⊥ (strict w2 refl)
    aux2 (eq w2) e2 (lt w3) =
      cart-pair-eq (refl , biinv-eq (funext (λ {(j , u) → aux7 j u (blinear _ _)})))
      module aux2-eq where
      aux5 : (j : Nat) → (u : j < n) →
             (a5 : BLinear (f e (j , u)) (k , w1)) →
             (w7 : fst (g-bnat-eqv.f-aux1-lt.aux3 k v e
                          w1 j (lt-suc-2 u) u a5) < k) →
             fst (g-bnat-eqv.f-aux1-lt.aux3 k v e w1 j (lt-suc-2 u) u a5) ≡
             fst (f e (j , u))
      aux5 j u (lt w5) _ = refl
      aux5 j u (eq w5) w7 = rec⊥ (strict (lt-suc-2 w7) (ap suc w5))
      aux5 j u (gt w5) w7 = rec⊥ (strict (lt-trans (lt-suc-2 w5) w7) refl)

      aux6 : (j : Nat) → (u : j < n) →
             (a6 : BLinear (f e (j , u)) (k , w1)) →
             (w7 : fst (g-bnat-eqv.f-aux1-lt.aux3 k v e
                          w1 j (lt-suc-2 u) u a6) > k) →
             pred (fst (g-bnat-eqv.f-aux1-lt.aux3 k v e
                          w1 j (lt-suc-2 u) u a6)) ≡
             fst (f e (j , u))
      aux6 j u (lt w6) w7 = rec⊥ (strict (lt-trans w6 w7) refl)
      aux6 j u (eq w6) w7 = refl
      aux6 j u (gt w6) w7 = refl

      aux7 : (j : Nat) → (u : j < n) →
             (a5 : BLinear (f (g-bnat-eqv.aux1 k v e (lt w1)) (j , lt-suc-2 u))
                           (f (g-bnat-eqv.aux1 k v e (lt w1)) (n , lt-suc-1))) →
             f-bnat-eqv.f-aux1-lt.aux2
               (g-bnat-eqv.aux1 k v e (lt w1)) w3 j u a5 ≡ f e (j , u)
      aux7 j u (lt w7) =
        bnat-eq (ap (λ b → fst (g-bnat-eqv.f-aux1-lt.aux2 k v e
                                   w1 j (lt-suc-2 u) b))
                    (blinear-β-lt u) ◾
                 aux5 j u (blinear _ _)
                      (tpt-lt (ap (λ b → fst (g-bnat-eqv.f-aux1-lt.aux2 k v e
                                                 w1 j (lt-suc-2 u) b))
                                  (blinear-β-lt u))
                              (ap (λ b → fst (g-bnat-eqv.f-aux1-lt.aux2 k v e
                                                 w1 n lt-suc-1 b))
                                  (blinear-β-eq refl)) w7))
      aux7 j u (eq w7) =
        rec⊥ (strict u
          (ap fst
              {x1 = j , lt-suc-2 u} {x2 = n , lt-suc-1}
              (! (bnat-eq
                   (g-bnat-eqv.η-aux1-lt.aux2 k v e w1 j (lt-suc-2 u)
                      (blinear
                       (g-bnat-eqv.f-aux1-lt.aux2 k v e w1 j (lt-suc-2 u)
                        (blinear (j , lt-suc-2 u) (n , lt-suc-1)))
                       (k , v)))) ◾
               ap (g (g-bnat-eqv.aux1 k v e (lt w1)))
                  {x1 = g-bnat-eqv.f-aux1-lt.aux2 k v e
                          w1 j (lt-suc-2 u) (blinear (j , lt-suc-2 u) (n , lt-suc-1))}
                  {x2 = g-bnat-eqv.f-aux1-lt.aux2 k v e
                          w1 n lt-suc-1 (blinear (n , lt-suc-1) (n , lt-suc-1))} 
                  (bnat-eq w7) ◾
               bnat-eq
                 (g-bnat-eqv.η-aux1-lt.aux2 k v e w1 n lt-suc-1
                  (blinear
                   (g-bnat-eqv.f-aux1-lt.aux2 k v e w1 n lt-suc-1
                    (blinear (n , lt-suc-1) (n , lt-suc-1)))
                   (k , v))))))
           
      aux7 j u (gt w7) =
        bnat-eq (ap (λ b → pred (fst (g-bnat-eqv.f-aux1-lt.aux2 k v e
                                         w1 j (lt-suc-2 u) b)))
                    (blinear-β-lt u) ◾
                 aux6 j u (blinear _ _)
                   (tpt-lt (ap (λ b → fst (g-bnat-eqv.f-aux1-lt.aux2 k v e
                                              w1 n lt-suc-1 b))
                               (blinear-β-eq refl))
                           (ap (λ b → fst (g-bnat-eqv.f-aux1-lt.aux2 k v e
                                              w1 j (lt-suc-2 u) b))
                               (blinear-β-lt u)) w7))

    aux2 (eq w2) e2 (eq w3) =
      cart-pair-eq
        (refl , biinv-eq (funext (λ {(j , u) →
          bnat-eq (ap (λ b → fst (g-bnat-eqv.f-aux1-lt.aux2 k v e
                              w1 j (lt-suc-2 u) b))
                      (blinear-β-lt u) ◾
                   ap (λ b → fst (g-bnat-eqv.f-aux1-lt.aux3 k v e
                                     w1 j (lt-suc-2 u) u b))
                      (blinear-β-lt (tpt-lt refl
                        (! w3 ◾
                         ap (λ b → fst (g-bnat-eqv.f-aux1-lt.aux2 k v e
                                           w1 n lt-suc-1 b))
                            (blinear-β-eq refl))
                        (snd (f e (j , u))))))})))

    aux2 (eq w2) e2 (gt w3) =
      rec⊥ (discrete-1 w3
        (snd (g-bnat-eqv.f-aux1-lt.aux2 k v e w1 n lt-suc-1
               (blinear (n , lt-suc-1) (n , lt-suc-1)))))

    aux2 (gt w2) _ _  = rec⊥ (strict w2 refl)

  aux1 (eq w1) = aux2 _ refl (blinear _ _)
    module aux1-eq where
    aux2 : (a2 : BLinear (n , lt-suc-1) (n , lt-suc-1)) →
           (e2 : blinear (n , lt-suc-1) (n , lt-suc-1)  ≡ a2) →
           (a3 : BLinear (f (g-bnat-eqv.aux1 k v e (eq w1)) (n , lt-suc-1))
                         (n , lt-suc-1)) →
           (g-bnat-eqv.f-aux1-eq.aux2 k v e w1 n lt-suc-1 a2 ,
            f-bnat-eqv.aux1 (g-bnat-eqv.aux1 k v e (eq w1)) a3) ≡ ((k , v) , e)
    aux2 (lt w2) _ _ = rec⊥ (strict w2 refl)
    
    aux2 (eq w2) e2 (lt w3) =
      rec⊥ (strict
        (tpt-lt (ap (λ b → fst (g-bnat-eqv.f-aux1-eq.aux2 k v e w1 n lt-suc-1 b)) e2)
                refl w3)
        refl)
    aux2 (eq w2) e2 (eq w3) =
      cart-pair-eq
        (bnat-eq (! w1) ,
         biinv-eq (funext (λ {(j , u) → bnat-eq (aux3 j u (blinear _ _))})))
      module aux2-eq where
      aux3 : (j : Nat) → (u : j < n) →
             (a3 : BLinear (j , lt-suc-2 u) (n , lt-suc-1)) →
             fst (g-bnat-eqv.f-aux1-eq.aux2 k v e w1 j (lt-suc-2 u) a3) ≡
             fst (f e (j , u))
      aux3 j u (lt w4) = ap (λ u → fst (f e (j , u))) (lt-is-prop w4 u)
      aux3 j u (eq w4) = rec⊥ (strict u w4)
      aux3 j u (gt w4) = rec⊥ (discrete-1 w4 (lt-suc-2 u))
      
    aux2 (eq w2) e2 (gt w3) =
      rec⊥ (discrete-1 w3
              (snd (g-bnat-eqv.f-aux1-eq.aux2 k v e w1 n lt-suc-1
                     (blinear (n , lt-suc-1) (n , lt-suc-1)))))
    
    aux2 (gt w2) _ _ = rec⊥ (strict w2 refl)
    
  aux1 (gt w1) = rec⊥ (discrete-1 w1 v)





bnat-suc-eqv : {n : Nat} → ⊤ ⊎ BNat n ≃ BNat (suc n)
bnat-suc-eqv {n} = eqv
  module bnat-suc-eqv where
  f-eqv : ⊤ ⊎ BNat n → BNat (suc n)
  f-eqv (inl _)       = n , lt-suc-1
  f-eqv (inr (m , w)) = m , lt-suc-2 w

  g-eqv : BNat (suc n) → ⊤ ⊎ BNat n
  g-eqv (k , v) = aux (blinear _ _) 
    module g-eqv where
    aux : BLinear (k , v) (n , lt-suc-1) → ⊤ ⊎ BNat n
    aux (lt w) = inr (k , w)
    aux (eq w) = inl _
    aux (gt w) = rec⊥ (discrete-1 w v)

  eqv : ⊤ ⊎ BNat n ≃ BNat (suc n)
  f eqv         = f-eqv
  g eqv         = g-eqv
  η eqv (inl _) = aux (blinear _ _)
    module η-eqv-l where
    aux : (a : BLinear (n , lt-suc-1) (n , lt-suc-1)) →
          g-eqv.aux n lt-suc-1 a ≡ inl _
    aux (lt w) = rec⊥ (strict w refl)
    aux (eq w) = refl
    aux (gt w) = rec⊥ (strict w refl)

  η eqv (inr (k , v)) = aux (blinear _ _)
    module η-eqv-r where
    aux : (a : BLinear (k , lt-suc-2 v) (n , lt-suc-1)) →
          g-eqv.aux k (lt-suc-2 v) a ≡ inr (k , v)
    aux (lt w) = ap inr (bnat-eq refl)
    aux (eq w) = rec⊥ (strict v w)
    aux (gt w) = rec⊥ (discrete-1 w (lt-suc-2 v))

  h eqv = g eqv

  ε eqv (k , v) = aux (blinear _ _)
    module ε-eqv where
    aux : (a : BLinear (k , v) (n , lt-suc-1)) →
          f-eqv (g-eqv.aux k v a) ≡ (k , v)
    aux (lt w) = bnat-eq refl
    aux (eq w) = bnat-eq (! w)
    aux (gt w) = rec⊥ (discrete-1 w v)
