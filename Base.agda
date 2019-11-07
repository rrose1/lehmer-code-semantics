{-# OPTIONS --without-K #-}
module Base where

open import Agda.Primitive
open import Agda.Builtin.Sigma public
open import Agda.Builtin.Equality public
open import Agda.Builtin.Unit public
open import Agda.Builtin.Bool public
open import Agda.Builtin.Nat hiding (_<_) public


variable
  l1 l2 l3 l4 l5 l6 : Level

infixr 6 _×_
_×_ : (X : Set l1) → (Y : Set l2) → Set (l1 ⊔ l2)
X × Y = Σ X (λ _ → Y)

data ⊥ : Set where

module _ {X : Set l1} where
  rec⊥ : ⊥ → X
  rec⊥ ()

module _ {X : Set l1} {Y : Set l2} (f : X → Y) where
  ap : {x1 x2 : X} → x1 ≡ x2 → f x1 ≡ f x2
  ap refl = refl

module _ {X : Set l1} where
  infixr 8 _◾_
  _◾_ : {x1 x2 : X} → x1 ≡ x2 → {x3 : X} → x2 ≡ x3 → x1 ≡ x3
  refl ◾ refl = refl

  ◾unitr : {x1 x2 : X} → {e : x1 ≡ x2} → e ◾ refl ≡ e
  ◾unitr {e = refl} = refl

  ◾unitl : {x1 x2 : X} → {e : x1 ≡ x2} → refl ◾ e ≡ e
  ◾unitl {e = refl} = refl

infixr 5 _⊎_
data _⊎_ {l1 l2} (X : Set l1) (Y : Set l2) : Set (l1 ⊔ l2) where
  inl : X → X ⊎ Y
  inr : Y → X ⊎ Y

infix 4 _≃_
record _≃_ (X : Set l1) (Y : Set l2) : Set (l1 ⊔ l2) where
  constructor biinv
  field
    f : X → Y
    g : Y → X
    η : (x : X) → g (f x) ≡ x
    h : Y → X
    ε : (y : Y) → f (h y) ≡ y
open _≃_ public

ide : (X : Set l1) → X ≃ X
f (ide X) x = x
g (ide X) = f (ide X)
η (ide X) x = refl
h (ide X) = g (ide X)
ε (ide X) x = refl



module _ {X : Set l1} where
  infix 10 !
  ! : {x1 x2 : X} → x1 ≡ x2 → x2 ≡ x1
  ! refl = refl

  !-eqv : {x1 x2 : X} → (x1 ≡ x2) ≃ (x2 ≡ x1)
  f !-eqv = !
  g !-eqv = !
  η !-eqv refl = refl
  h !-eqv = g !-eqv
  ε !-eqv = η !-eqv

  !! : {x1 x2 : X} → {e : x1 ≡ x2} → ! (! e) ≡ e
  !! {e = e} = η !-eqv e

module _ {X : Set l1} (P : X → Set l2) where
  tpt-eqv : {x1 x2 : X} → (e : x1 ≡ x2) → P x1 ≃ P x2
  f (tpt-eqv refl) p = p 
  g (tpt-eqv e)    p = f (tpt-eqv (! e)) p
  η (tpt-eqv refl) p = refl
  h (tpt-eqv e)      = g (tpt-eqv e)
  ε (tpt-eqv refl) p = refl

  tpt : {x1 x2 : X} → (e : x1 ≡ x2) → P x1 → P x2
  tpt e = f (tpt-eqv e)

module _ {X : Set l1} (P : X → Set l2) (f : (x : X) → P x) where
  apd : {x1 x2 : X} → (e : x1 ≡ x2) → tpt P e (f x1) ≡ f x2
  apd refl = refl


module _ {X : Set l1} {Y : Set l2} (Q : X → Y → Set l3) where
  tpt2-cart-eqv : {x1 x2 : X} → (e1 : x1 ≡ x2) →
                  {y1 y2 : Y} → (e2 : y1 ≡ y2) →
                  Q x1 y1 ≃ Q x2 y2
  f (tpt2-cart-eqv refl refl) q = q
  g (tpt2-cart-eqv e1 e2)       = f (tpt2-cart-eqv (! e1) (! e2))
  η (tpt2-cart-eqv refl refl) q = refl
  h (tpt2-cart-eqv e1 e2)       = g (tpt2-cart-eqv e1 e2)
  ε (tpt2-cart-eqv refl refl) q = refl


module _ {X : Set l1} where
  lcomp-eqv : {x1 x2 : X} → (e1 : x1 ≡ x2) → {x3 : X} → (x2 ≡ x3) ≃ (x1 ≡ x3)
  f (lcomp-eqv e1) e2 = e1 ◾ e2
  g (lcomp-eqv e1) e2 = ! e1 ◾ e2
  η (lcomp-eqv refl) refl = refl
  h (lcomp-eqv e1)     = g (lcomp-eqv e1)
  ε (lcomp-eqv refl) refl = refl

  lcomp-τ : {x1 x2 : X} → (e1 : x1 ≡ x2) → {x3 : X} → (e2 : x2 ≡ x3) →
            ap (f (lcomp-eqv e1)) (η (lcomp-eqv e1) e2) ≡
            ε (lcomp-eqv e1) (f (lcomp-eqv e1) e2)
  lcomp-τ refl refl = refl

  lcomp-ν : {x1 x2 : X} → (e1 : x1 ≡ x2) → {x3 : X} → (e2 : x1 ≡ x3) →
            ap (g (lcomp-eqv e1)) (ε (lcomp-eqv e1) e2) ≡
            η (lcomp-eqv e1) (g (lcomp-eqv e1) e2)
  lcomp-ν refl refl = refl

  lwhisk-coh : {x1 x2 : X} → {e1 e2 : x1 ≡ x2} → (e4 : e1 ≡ e2) →
         ap (λ e2 → refl ◾ e2) e4 ≡
         f (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitl) (! ◾unitl)) e4
  lwhisk-coh {e1 = refl} refl = refl

  lwhisk-eqv : {x1 x2 : X} → {e1 : x1 ≡ x2} →
               {x3 : X} → {e2 e3 : x2 ≡ x3} →
               (e2 ≡ e3) ≃ (e1 ◾ e2 ≡ e1 ◾ e3)
  f (lwhisk-eqv {e1 = e1}) = ap (f (lcomp-eqv e1))
  g (lwhisk-eqv {e1 = refl}) =
    g (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitl) (! ◾unitl))
  η (lwhisk-eqv {e1 = refl}) e4 =
    ap (f (tpt2-cart-eqv _≡_ (! (! ◾unitl)) (! (! ◾unitl)))) (lwhisk-coh e4) ◾
    η (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitl) (! ◾unitl)) e4
  h lwhisk-eqv               = g (lwhisk-eqv)
  ε (lwhisk-eqv {e1 = refl}) e4 =
    lwhisk-coh (f (tpt2-cart-eqv _≡_ (! (! ◾unitl)) (! (! ◾unitl))) e4) ◾
    ε (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitl) (! ◾unitl)) e4

  lwhisk-τ : {x1 x2 : X} → {e1 : x1 ≡ x2} →
             {x3 : X} → {e2 e3 : x2 ≡ x3} →
             (e4 : e2 ≡ e3) →
             ap (f (lwhisk-eqv {e1 = e1})) (η (lwhisk-eqv {e1 = e1}) e4) ≡
             ε lwhisk-eqv (f lwhisk-eqv e4)
  lwhisk-τ {e1 = refl} {e2 = refl} refl = refl

  rcomp-eqv : {x1 x2 : X} → (e1 : x1 ≡ x2) → {x3 : X} → (x3 ≡ x1) ≃ (x3 ≡ x2)
  f (rcomp-eqv e1) e2 = e2 ◾ e1
  g (rcomp-eqv e1) e2 = e2 ◾ ! e1
  η (rcomp-eqv refl) refl = refl
  h (rcomp-eqv e1)      = g (rcomp-eqv e1)
  ε (rcomp-eqv refl) refl = refl

  rwhisk-coh : {x1 x2 : X} → {e1 e2 : x1 ≡ x2} → (e4 : e1 ≡ e2) →
               ap (λ e2 → e2 ◾ refl) e4 ≡
               f (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitr) (! ◾unitr)) e4
  rwhisk-coh {e1 = refl} refl = refl

  rwhisk-eqv : {x1 x2 : X} → {e1 : x1 ≡ x2} →
               {x3 : X} → {e2 e3 : x3 ≡ x1} →
               (e2 ≡ e3) ≃ (e2 ◾ e1 ≡ e3 ◾ e1)
  f (rwhisk-eqv {e1 = e1}) = ap (f (rcomp-eqv e1))  
  g (rwhisk-eqv {e1 = refl}) =
    g (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitr) (! ◾unitr))
  η (rwhisk-eqv {e1 = refl}) e4 =
    ap (f (tpt2-cart-eqv _≡_ (! (! ◾unitr)) (! (! ◾unitr)))) (rwhisk-coh e4) ◾
    η (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitr) (! ◾unitr)) e4
  h rwhisk-eqv               = g (rwhisk-eqv)
  ε (rwhisk-eqv {e1 = refl}) e4 =
    rwhisk-coh (f (tpt2-cart-eqv _≡_ (! (! ◾unitr)) (! (! ◾unitr))) e4) ◾
    ε (tpt2-cart-eqv (λ x1 x2 → x1 ≡ x2) (! ◾unitr) (! ◾unitr)) e4

module _ {X : Set l1} {P : X → Set l2} where
  ap-snd : {x1 x2 : X} → {p1 : P x1} → {p2 : P x2} →
           (e : _≡_ {A = Σ X P} (x1 , p1) (x2 , p2)) →
           tpt P (ap fst e) p1 ≡ p2
  ap-snd refl = refl

module _ {X : Set l1} {x0 : X} where
  tpt-const-eq-var : {x1 x2 : X} → (e1 : x1 ≡ x2) → (e2 : x0 ≡ x1) →
                     tpt (λ x → x0 ≡ x) e1 e2 ≡ e2 ◾ e1
  tpt-const-eq-var refl refl = refl

  tpt-var-eq-const : {x1 x2 : X} → (e1 : x1 ≡ x2) → (e2 : x1 ≡ x0) →
                     tpt (λ x → x ≡ x0) e1 e2 ≡ ! e1 ◾ e2
  tpt-var-eq-const refl refl = refl

module _ {X : Set l1} {Y : Set l2}
         {f : X → Y} {g : Y → X}
         (η : (x : X) → g (f x) ≡ x)
         where
  inv-sq : {x1 x2 : X} → (e1 : x1 ≡ x2) →
           ! (η x1) ◾ ap g (ap f e1) ◾ η x2 ≡ e1
  inv-sq {x1} = coh2
    module inv-sq where
    coh1 : {x1 x2 : X} → (e : x1 ≡ x2) → ! e ◾ refl ◾ e ≡ refl
    coh1 refl = refl

    coh2 = λ { refl → coh1 (η _) }

  inv-comm : (x : X) → ap g (ap f (η x)) ≡ η (g (f x))
  inv-comm x1 = _≃_.g rwhisk-eqv (coh (η x1))
    module inv-comm where
    coh : {x1 x2 : X} → (e1 : x1 ≡ x2) → ap g (ap f e1) ◾ η x2 ≡ η x1 ◾ e1
    coh refl = ◾unitl ◾ ! ◾unitr

module _ where
  is-contr : Set l1 → Set l1
  is-contr X = Σ X (λ x0 → (x : X) → x ≡ x0)

  is-prop : Set l1 → Set l1
  is-prop X = (x1 x2 : X) → x1 ≡ x2

  is-set : Set l1 → Set l1
  is-set X = {x1 x2 : X} → (e1 e2 : x1 ≡ x2) → e1 ≡ e2

module _ where
  prop-is-set : {X : Set l1} → is-prop X → is-set X
  prop-is-set ϕ {x1} {x2} e1 e2 =
    g lwhisk-eqv
      (! (tpt-const-eq-var e1 (ϕ x1 x1)) ◾
       apd _ (ϕ x1) e1 ◾
       ! (apd _ (ϕ x1) e2)
       ◾ tpt-const-eq-var e2 (ϕ x1 x1))

module _ {X : Set l1} {P : X → Set l2} where
  pair-eqv : {x1 x2 : X} → {p1 : P x1} → {p2 : P x2} →
             (Σ (x1 ≡ x2) (λ p → tpt P p p1 ≡ p2)) ≃
             ((x1 , p1) ≡ (x2 , p2))
  f pair-eqv (refl , refl)  = refl
  g pair-eqv e1             = ap fst e1 , ap-snd e1
  η pair-eqv (refl , refl)  = refl
  h pair-eqv                = g pair-eqv
  ε pair-eqv refl           = refl

  pair-eq = λ {x1} {x2} {p1} {p2} → f (pair-eqv {x1} {x2} {p1} {p2})

module _ {X : Set l1} {Y : Set l2} where
  cart-pair-eqv : {x1 x2 : X} → {y1 y2 : Y} →
                  ((x1 ≡ x2) × (y1 ≡ y2)) ≃ ((x1 , y1) ≡ (x2 , y2))
  f cart-pair-eqv (refl , refl)  = refl
  g cart-pair-eqv             e1 = ap fst e1 , ap snd e1
  η cart-pair-eqv (refl , refl)  = refl
  h cart-pair-eqv                = g cart-pair-eqv
  ε cart-pair-eqv refl           = refl

  cart-pair-eq = λ {x1} {x2} {y1} {y2} → f (cart-pair-eqv {x1} {x2} {y1} {y2})


module EquivCoh {X : Set l1} {Y : Set l2} where
  ε' : (e : X ≃ Y) → (y : Y) → f e (g e y) ≡ y
  ε' e y = ! (ap (λ y → f e (g e y)) (ε e y)) ◾ ap (f e) (η e (h e y)) ◾ ε e y

  η' : (e : X ≃ Y) → (x : X) → h e (f e x) ≡ x
  η' e x = ! (η e (h e (f e x))) ◾ ap (g e) (ε e (f e x)) ◾ η e x

open EquivCoh public


module _ {X : Set l1} {Y : Set l2} {Z : Set l3}
         (e1 : Y ≃ Z) (e2 : X ≃ Y)
         where
  infixr 5 _∘e_
  _∘e_ : X ≃ Z
  f _∘e_ x = f e1 (f e2 x)
  g _∘e_ z = g e2 (g e1 z)
  η _∘e_ x = ap (g e2) (η e1 (f e2 x)) ◾ η e2 x
  h _∘e_ z = h e2 (h e1 z)
  ε _∘e_ z = ap (f e1) (ε e2 (h e1 z)) ◾ ε e1 z

module _ {X : Set l1} {Y : Set l2} (e : X ≃ Y) where
  !e : Y ≃ X
  f !e = g e
  g !e = f e
  η !e = ε' e
  h !e = f e
  ε !e = η e

module _ {X : Set l1} {P : X → Set l2} {f g : (x : X) → P x} where
  postulate
    funext : ((x : X) → f x ≡ g x) → f ≡ g
    funext-happly : (e : f ≡ g) → funext (λ x → ap (λ f → f x) e) ≡ e
    happly-funext : (ϕ : ((x : X) → f x ≡ g x)) →
                    (λ x → ap (λ f → f x) (funext ϕ)) ≡ ϕ

  happly-eqv : (f ≡ g) ≃ ((x : X) → f x ≡ g x)
  _≃_.f happly-eqv e x = ap (λ a → a x) e
  _≃_.g happly-eqv = funext 
  _≃_.η happly-eqv = funext-happly
  _≃_.h happly-eqv = _≃_.g happly-eqv
  _≃_.ε happly-eqv = happly-funext

module _ {X : Set l1} where
  contr-is-prop : is-contr X → is-prop X
  contr-is-prop (x , ϕ) x1 x2 = ϕ x1 ◾ ! (ϕ x2)

module _ {X : Set l1} where
  is-contr-is-contr : is-contr X → is-contr (is-contr X)
  is-contr-is-contr (x0 , ϕ0) =
    (x0 , ϕ0) ,
    (λ {(x1 , ϕ1) →
        pair-eq
        (ϕ0 x1 ,
         funext (λ x2 →
           prop-is-set
             (contr-is-prop (x0 , ϕ0))
             (tpt (λ x3 → (x : X) → x ≡ x3) (ϕ0 x1) ϕ1 x2) (ϕ0 x2))) })

module _ {X : Set l1} {Y : Set l2} (e : X ≃ Y) where
  is-contr-eqv : (is-contr X) ≃ (is-contr Y)
  f is-contr-eqv (x , ϕ) =
    f e x , (λ y → ! (ε e y) ◾ ! (ap (f e) (! (ϕ (h e y)))))
  g is-contr-eqv (y , ϕ) =
    g e y , (λ x → ! (η e x) ◾ ! (ap (g e) (! (ϕ (h (!e e) x)))))
  η is-contr-eqv (x , ϕ) = snd (is-contr-is-contr (x , ϕ)) (_ , _)
  h is-contr-eqv = g is-contr-eqv
  ε is-contr-eqv (y , ϕ) = snd (is-contr-is-contr (y , ϕ)) (_ , _)

module _ {X : Set l1}
         {P : X → Set l2} {Q : X → Set l3}
         (ϕ : (x : X) → P x ≃ Q x)
         where
  sigma-eqv-2 : (Σ X P) ≃ (Σ X Q)
  f sigma-eqv-2 (x , p) = x , f (ϕ x) p
  g sigma-eqv-2 (x , q) = x , g (ϕ x) q
  η sigma-eqv-2 (x , p) = pair-eq (refl , η (ϕ x) p)
  h sigma-eqv-2 (x , q) = x , h (ϕ x) q
  ε sigma-eqv-2 (x , q) = pair-eq (refl , ε (ϕ x) q)

-----------

module _ {X : Set l1} {Y : Set l2} {Z : Set l3} where
  flip-eqv : (X → Y → Z) ≃ (Y → X → Z)
  f flip-eqv k y x = k x y
  g flip-eqv k x y = k y x
  η flip-eqv k = refl
  h flip-eqv = g flip-eqv
  ε flip-eqv k = refl

  flip : (X → Y → Z) → (Y → X → Z)
  flip = f flip-eqv

module _ {X : Set l1} {Y : Set l2}
         (f : X → Y) (g : Y → X)
         (η : (x : X) → g (f x) ≡ x)
         (ε : (y : Y) → f (g y) ≡ y)
         where
  qinv-is-cfn : (y : Y) → is-contr (Σ X (λ x → f x ≡ y))
  fst (qinv-is-cfn y) = g y , ε y
  snd (qinv-is-cfn y) (x , e) =
    pair-eq (! (η x) ◾ ! (ap g (ε (f x))) ◾ ap g (ap f (η x)) ◾ ap g e ,
             coh1 (η x) (ap g (ε (f x))) (ap g (ap f (η x))) (ap g e) e ◾
             coh2 e (η x))
    module qinv-is-cfn where
    coh1 : {x1 x2 x3 x4 x5 : X} → {y1 : Y} →
           (p1 : x1 ≡ x2) → (p2 : x3 ≡ x1) → (p3 : x3 ≡ x4) →
           (p4 : x4 ≡ x5) → (p5 : f x2 ≡ y1) →
           tpt (λ x → f x ≡ y1) (! p1 ◾ ! p2 ◾ p3 ◾ p4) p5 ≡
           ! (ap f p4) ◾ ! (ap f p3) ◾ ap f p2 ◾ ap f p1 ◾ p5
    coh1 refl refl refl refl refl = refl

    coh2 : {x1 x2 : X} → {y1 : Y} →
           (e1 : f x2 ≡ y1) →
           (e2 : g (f x1) ≡ x2) →
           ! (ap f (ap g e1)) ◾
           ! (ap f (ap g (ap f e2))) ◾
           ap f (ap g (ε (f x1))) ◾
           ap f e2 ◾
           e1 ≡ ε y1
    coh2 {x1} refl refl = ◾unitl ◾ ◾unitl ◾ ◾unitr ◾ inv-comm ε (f x1) 


module _ {W : Set l1} {X : Set l2} {Y : Set l3} where
  qinv-is-cfn-2 : (k1 : W → X → Y) → (k2 : W → Y) →
                  (k3 : (W → Y) → X) →
                  (ϕ1 : (x : X) → k3 (λ w → k1 w x) ≡ x) →
                  (ϕ2 : (k2 : W → Y) → (λ w → k1 w (k3 k2)) ≡ k2) →
                  is-contr (Σ X (λ x → (w : W) → k1 w x ≡ k2 w))
  qinv-is-cfn-2 k1 k2 k3 ϕ1 ϕ2 =
    f (is-contr-eqv (sigma-eqv-2 (λ _ → happly-eqv)))
      (qinv-is-cfn (flip k1) k3 ϕ1 ϕ2 k2)


module _ {X : Set l1} {Y : Set l2} where
  biinv-eq : {e1 e2 : X ≃ Y} → f e1 ≡ f e2 → e1 ≡ e2
  biinv-eq {e1@(biinv _ g1 η1 h1 ε1)} {biinv f2 g2 η2 h2 ε2} refl =
    ap (λ w → biinv f2 (fst w) (snd w) h1 ε1)
      (contr-is-prop
        (qinv-is-cfn-2
          (λ x g → g (f2 x)) (λ x → x) (λ k y → k (h1 y))
          (λ g3 → funext (λ y → ap g3 (ε1 y)))
          (λ k → funext (λ x → ap k (η' e1 x)))) _ _) ◾
    ap (λ w → biinv f2 g2 η2 (fst w) (snd w))
      (contr-is-prop
        (qinv-is-cfn-2
          (λ y h → f2 (h y)) (λ x → x) (λ k y → g1 (k y))
          (λ g3 → funext (λ y → η1 (g3 y)))
          (λ k → funext (λ y → ε' e1 (k y)))) _ _)
      
----------

module _ {W : Set l1} {X : Set l2} {Y : Set l3} {Z : Set l4}
         (e1 : Y ≃ Z) (e2 : X ≃ Y) (e3 : W ≃ X) where
  ∘e-assoc : (e1 ∘e e2) ∘e e3 ≡ e1 ∘e e2 ∘e e3
  ∘e-assoc = biinv-eq refl

module _ {X : Set l1} {Y : Set l2} (e : X ≃ Y) where
  ∘e-unitl : ide Y ∘e e ≡ e
  ∘e-unitl = biinv-eq refl

  ∘e-unitr : e ∘e ide X ≡ e
  ∘e-unitr = biinv-eq refl

  ∘e-invl : !e e ∘e e ≡ ide X
  ∘e-invl = biinv-eq (funext (η e))
  
  ∘e-invr : e ∘e !e e ≡ ide Y
  ∘e-invr = biinv-eq (funext (ε' e))

module _ {X : Set l1} {Y : Set l2} {Z : Set l3} (e1 : X ≃ Y) where
  ∘e-precomp-eqv : (Y ≃ Z) ≃ (X ≃ Z)
  f ∘e-precomp-eqv e2 = e2 ∘e e1
  g ∘e-precomp-eqv e2 = e2 ∘e !e e1
  η ∘e-precomp-eqv e2 =
    ∘e-assoc e2 e1 (!e e1) ◾
    ap (λ e → e2 ∘e e) (∘e-invr e1) ◾
    ∘e-unitr e2 
  h ∘e-precomp-eqv = g ∘e-precomp-eqv
  ε ∘e-precomp-eqv e2 =
    ∘e-assoc e2 (!e e1) e1 ◾
    ap (λ e → e2 ∘e e) (∘e-invl e1) ◾
    ∘e-unitr e2 

module _ {X : Set l1} {Y : Set l2} {Z : Set l3} (e1 : Y ≃ Z) where
  ∘e-postcomp-eqv : (X ≃ Y) ≃ (X ≃ Z)
  f ∘e-postcomp-eqv e2 = e1 ∘e e2
  g ∘e-postcomp-eqv e2 = !e e1 ∘e e2
  η ∘e-postcomp-eqv e2 =
    ! (∘e-assoc (!e e1) e1 e2) ◾
    ap (λ e → e ∘e e2) (∘e-invl e1) ◾
    ∘e-unitl e2
  h ∘e-postcomp-eqv = g ∘e-postcomp-eqv
  ε ∘e-postcomp-eqv e2 =
    ! (∘e-assoc e1 (!e e1) e2) ◾
    ap (λ e → e ∘e e2) (∘e-invr e1) ◾
    ∘e-unitl e2

module _ {W : Set l1} {X : Set l2} {Y : Set l3} {Z : Set l4}
         (e1 : W ≃ X) (e2 : Y ≃ Z)
         where
  ∘e-bicomp-eqv : (X ≃ Y) ≃ (W ≃ Z)
  ∘e-bicomp-eqv = ∘e-postcomp-eqv e2 ∘e ∘e-precomp-eqv e1


module _ {X1 : Set l1} {X2 : Set l2} {Y1 : Set l3} {Y2 : Set l4}
         (e1 : X1 ≃ Y1) (e2 : X2 ≃ Y2) where
  infixr 6 _×e_
  _×e_ : (X1 × X2) ≃ (Y1 × Y2)
  f _×e_ (x1 , x2) = f e1 x1 , f e2 x2
  g _×e_ (y1 , y2) = g e1 y1 , g e2 y2
  η _×e_ (x1 , x2) = cart-pair-eq (η e1 x1 , η e2 x2)
  h _×e_ (y1 , y2) = h e1 y1 , h e2 y2
  ε _×e_ (y1 , y2) = cart-pair-eq (ε e1 y1 , ε e2 y2)


module _ {X : Set l1} {Y : Set l2} (n : X → ⊥) where
  ⊎-unitl : (X ⊎ Y) ≃ Y
  f ⊎-unitl (inl x) = rec⊥ (n x)
  f ⊎-unitl (inr y) = y
  g ⊎-unitl         = inr
  η ⊎-unitl (inl x) = rec⊥ (n x)
  η ⊎-unitl (inr y) = refl
  h ⊎-unitl         = g ⊎-unitl
  ε ⊎-unitl _       = refl

module _ {X : Set l1} {Y : Set l2} (n : Y → ⊥) where
  ⊎-unitr : (X ⊎ Y) ≃ X
  f ⊎-unitr (inl x) = x
  f ⊎-unitr (inr y) = rec⊥ (n y)
  g ⊎-unitr         = inl
  η ⊎-unitr (inl x) = refl
  η ⊎-unitr (inr y) = rec⊥ (n y)
  h ⊎-unitr         = g ⊎-unitr
  ε ⊎-unitr _       = refl

module _ {X : Set l1} {Y : Set l2} {Z : Set l3} where
  ⊎-assoc : ((X ⊎ Y) ⊎ Z) ≃ (X ⊎ Y ⊎ Z)
  f ⊎-assoc (inl (inl x)) = inl x
  f ⊎-assoc (inl (inr y)) = inr (inl y)
  f ⊎-assoc (inr z) = inr (inr z)
  g ⊎-assoc (inl x) = inl (inl x)
  g ⊎-assoc (inr (inl y)) = inl (inr y)
  g ⊎-assoc (inr (inr z)) = inr z
  η ⊎-assoc (inl (inl x)) = refl
  η ⊎-assoc (inl (inr y)) = refl
  η ⊎-assoc (inr z) = refl
  h ⊎-assoc = g ⊎-assoc
  ε ⊎-assoc (inl x) = refl
  ε ⊎-assoc (inr (inl y)) = refl
  ε ⊎-assoc (inr (inr z)) = refl

module _ {X : Set l1} {Y : Set l2} where
  ⊎-com : (X ⊎ Y) ≃ (Y ⊎ X)
  f ⊎-com (inl x) = inr x
  f ⊎-com (inr y) = inl y
  g ⊎-com (inl y) = inr y
  g ⊎-com (inr x) = inl x
  η ⊎-com (inl x) = refl
  η ⊎-com (inr y) = refl
  h ⊎-com = g ⊎-com
  ε ⊎-com (inl y) = refl
  ε ⊎-com (inr x) = refl

module _ {X1 : Set l1} {X2 : Set l2} {Y1 : Set l3} {Y2 : Set l4}
         (e1 : X1 ≃ Y1) (e2 : X2 ≃ Y2) where
  infixr 5 _⊎e_
  _⊎e_ : (X1 ⊎ X2) ≃ (Y1 ⊎ Y2)
  f _⊎e_ (inl x) = inl (f e1 x)
  f _⊎e_ (inr y) = inr (f e2 y)
  g _⊎e_ (inl x) = inl (g e1 x)
  g _⊎e_ (inr y) = inr (g e2 y)
  η _⊎e_ (inl x) = ap inl (η e1 x)
  η _⊎e_ (inr y) = ap inr (η e2 y)
  h _⊎e_ (inl x) = inl (h e1 x)
  h _⊎e_ (inr y) = inr (h e2 y)
  ε _⊎e_ (inl x) = ap inl (ε e1 x)
  ε _⊎e_ (inr y) = ap inr (ε e2 y)
