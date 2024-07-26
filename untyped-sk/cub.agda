{-# OPTIONS --cubical #-}

-- open import Cubical
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Data.Fin 
open import Cubical.Data.Vec
-- data ℤ : Set where
--     zero : ℤ
--     suc pred : ℤ → ℤ
--     sucpred : ∀ n → suc (pred n) ≡ n
--     predsuc : ∀ n → pred (suc n) ≡ n

-- refl' : ∀{ℓ}{A : Type ℓ}{a : A} → a ≡ a
-- refl' {a = a} Id = a

-- sym' : ∀{ℓ}{A : Type ℓ}{a b : A} → a ≡ b → b ≡ a
-- sym' {a = a} {b = b} x Id = x (~ i)

-- _+_ : ℤ → ℤ → ℤ
-- zero + k = k 
-- suc n + k = suc (n + k)
-- pred n + k = pred(n + k)
-- sucpred n Id + k = sucpred (n + k) i
-- predsuc n Id + k = predsuc (n + k) i

-- _-_ : ℤ → ℤ → ℤ
-- x - zero = x
-- x - suc y = pred (x - y)
-- x - pred y = suc (x - y)
-- x - sucpred y Id = predsuc (x - y) i
-- x - predsuc y Id = sucpred (x - y) i

-- _*_ :  ℤ → ℤ → ℤ
-- zero * y = zero
-- suc x * y = y + (x * y)
-- pred x * y = (x * y) - y
-- sucpred x Id * y = {!   !}
-- predsuc x Id * y = {!   !}

-- f : {Id j k : I}(P : Id → Type) → P ((Id ∧ j) ∨ k) → P ((Id ∨ k) ∧ (j ∨ k))
-- f P v = v

{- 
Min
i0 ∧ Id ≝ i0 ≝ Id ∧ i0
i1 ∧ Id ≝ Id ≝ Id ∧ i1

Id ∧ Id ≝ i
Id ∧ j ≝ j ∧ i

λ Id → Id ∧ ~ Id 

Max 
λ (Id : I) → i0 ∨ Id ≝ λ Id → Id ≝ λ (Id : I) → Id ∨ i0 
λ (Id : I) → i1 ∨ Id ≝ λ Id → i1 ≝ λ (Id : I) → Id ∨ i1 
λ (Id j : I) → Id ∨ j ≝ j ∨ i
λ (Id : I) → Id ∨ Id ≝ i

Sym (~)
~ i0 ≝ i1
~ i1 ≝ i0
~ (~ i) ≝ i

~ (Id ∧ j) ≝ ~ Id ∨ ~ j
~ (Id ∨ j) ≝ ~ Id ∧ ~ j
(Id ∧ j) ∨ k ≝ (Id ∨ k) ∧ (j ∨ k)
(Id ∨ j) ∧ k ≝ (Id ∧ k) ∨ (j ∧ k)

Id | j | ~ (Id ∧ j) | (~ i) ∨ (~ j)
⊤ | ⊤ | ⊥        |  ⊥        
⊤ | ⊥ | ⊤        |  ⊤
⊥ | ⊤ | ⊤        |  ⊤
⊥ | ⊥ | ⊤        |  ⊤

Id | j | ~ (Id ∨ j) | (~ i) ∧ (~ j)
⊤ | ⊤ | ⊥        |  ⊥        
⊤ | ⊥ | ⊥        |  ⊥
⊥ | ⊤ | ⊥        |  ⊥
⊥ | ⊥ | ⊤        |  ⊤ 

Id | j | k | Id ∧ j | (Id ∧ j) ∨ k | (Id ∨ k) ∧ (j ∨ k)
⊤ | ⊤ | ⊤ | ⊤    |  ⊤
⊤ | ⊤ | ⊥ | T    |  ⊤      
⊤ | ⊥ | ⊤ | ⊥    |  ⊤
⊤ | ⊥ | ⊥ | ⊥    |  ⊥ 
⊥ | ⊤ | ⊤ | ⊥    |  ⊤
⊥ | ⊤ | ⊥ | ⊥    |  ⊥
⊥ | ⊥ | ⊤ | ⊥    |  ⊤ 
⊥ | ⊥ | ⊥ | ⊥    |  ⊥ 

-}

record Model : Set₁ where
  infixl 5 _·_ 
  field
    Tm  : Set
    _·_ : Tm → Tm → Tm
    K S : Tm
    Kβ  : ∀{u f} → K · u · f ≡ u
    Sβ  : ∀{f g u} → S · f · g · u ≡ f · u · (g · u)

module notFiniteModel
  (m : ℕ)
  (_·_ :  Fin (suc (suc m)) → Fin (suc (suc m)) → Fin (suc (suc m)))
  (let infixl 5 _·_; _·_ = _·_)
  (K S :  Fin (suc (suc m)))
  (Kβ : {u f : Fin (suc (suc m))} → (K · u) · f ≡ u)
  (Sβ :  {f g u : Fin (suc (suc m))} → ((S · f) · g) · u ≡ (f · u) · (g · u))

  where

    n = suc (suc m)
    Tm = Fin n

    infixl 5 _·s_
    
    Id : Tm
    Id = S · K · K
    Iβ : ∀{u} → Id · u ≡ u
    Iβ {u} =
        (S · K · K · u)
                ≡⟨ Sβ ⟩ 
        (K · u · (K · u))
                ≡⟨ Kβ ⟩ 
        refl

    B : Tm
    B = S · (K · S) · K
    Bβ : ∀{f g u} → B · f · g · u ≡ f · (g · u)
    Bβ {f}{g}{u} = 
        (S · (K · S) · K · f · g · u)
                ≡⟨ cong (λ z → z · g · u) Sβ ⟩ 
        (K · S · f · (K · f) · g · u)
                ≡⟨ cong (λ z → z · (K · f) · g · u) Kβ ⟩ 
        (S · (K · f) · g · u)
                ≡⟨ Sβ ⟩ 
        (K · f · u · (g · u))
                ≡⟨ cong (λ z → z · (g · u)) Kβ ⟩ 
        refl

    C : Tm
    C = S · (S · (K · B) · S) · (K · K)
    Cβ : ∀{f g u} → C · f · u · g ≡ f · g · u
    Cβ {f}{g}{u} = 
        (S · (S · (K · B) · S) · (K · K) · f · u · g)
                ≡⟨ cong (λ z → z · u · g) Sβ ⟩ 
        (S · (K · B) · S · f · (K · K · f) · u · g)
                ≡⟨ cong (λ z → z · ((K · K) · f) · u · g) Sβ ⟩ 
        (K · B · f · (S · f) · (K · K · f) · u · g)
                ≡⟨ cong (λ z → z · (S · f) · (K · K · f) · u · g) Kβ ⟩ 
        (B · (S · f) · (K · K · f) · u · g)
                ≡⟨ cong (λ z → z · g) Bβ ⟩ 
        (S · f · (K · K · f · u) · g)
                ≡⟨ Sβ ⟩ 
        (f · g · (K · K · f · u · g))
                ≡⟨ cong (λ z → f · g · (z · u · g)) Kβ ⟩ 
        (f · g · (K · u · g))
                ≡⟨ cong (λ z → f · g · z) Kβ ⟩ 
        refl

    Zero : Tm 
    Zero = K · Id
    Zeroβ :  ∀{f x} → Zero · f · x ≡ x
    Zeroβ {f}{x} = 
        (K · Id · f · x)
                ≡⟨ cong (λ z → z · x) Kβ  ⟩ 
        (Id · x)
                ≡⟨ Iβ ⟩ 
        refl

    One : Tm 
    One = Id
    Oneβ : ∀{f x} → One · f · x ≡ f · x
    Oneβ {f}{x} = 
        (Id · f · x)
                ≡⟨ cong (λ z → z · x) Iβ ⟩ 
        refl

    Suc : Tm 
    Suc = S · B 
    Sucβ : ∀{n f x} → Suc · n · f · x ≡ f · (n · f · x)
    Sucβ {n}{f}{x} = 
        (S · B · n · f · x)
                ≡⟨ cong (λ z → z · x) Sβ ⟩ 
        (B · f · (n · f) · x)
                ≡⟨ Bβ ⟩ 
        refl

    _·s_ : Tm → {n : ℕ} → Vec Tm n → Tm
    _·s_ t {zero}  [] = t
    _·s_ t {suc n} (u ∷ us)  = t · u ·s us

    -- lookup : {A : Set }{n : ℕ} → Vec A n → Fin n → A
    -- lookup (x ∷ xs) fzero    = x
    -- lookup (x ∷ xs) (fsuc i) = lookup xs i
    
--     -- {!   !}
--     --           ≡⟨ {!   !} ⟩ 
--     -- {!   !}
--     --           ≡⟨ {!   !} ⟩ 
--     -- {!   !}
--     --           ≡⟨ {!  !} ⟩ 
--     -- {!   !}
    --     m≤sucm : {m : ℕ} → m < (suc m)
    -- m≤sucm {zero} = s≤s z≤n
    -- m≤sucm {suc m} = s≤s m≤sucm

    almost0 : {j : Fin (suc n)} → Fin (suc n) → Tm
    almost0 {j} x = {!   !}

    flatten : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (Fin n → A) → Vec A n
    flatten {n = zero}  f = []
    flatten {n = suc n} f = f fzero ∷ flatten {n = n} {! hcomp f fsuc  !} --flatten {n = n} (f  fsuc)

    us : {j : Fin (suc n)} → Vec Tm (suc n)
    us {j} = flatten (almost0 {j})
    
    proj : ∀(i : ℕ) → Fin (suc i) → Tm
    proj zero f = Id
    proj (suc i) (zero , c) = B · K · proj i fzero --(zero , {! snd₁  !})
    proj (suc i) (suc j , c) = K · proj i (predFin  i  ((suc j , c)))
    -- proj (suc zero)    fzero    = I
    -- proj (suc (suc n)) fzero    = B · K · proj (suc n) fzero
    -- proj (suc (suc n)) (fsuc x) = K · proj (suc n) x

--     projβ : (n : ℕ)(x : Fin (suc n))(us : Vec Tm (suc n)) → proj n x ·s us ≡ lookup us x
--     projβ = ?
    --  (suc zero)    fzero    (u ∷ [])      = Iβ
    -- projβ (suc (suc n)) fzero    (u ∷ u' ∷ us) = trans (cong (λ x → x · u' ·s us) Bβ) (trans (cong (_·s us) Kβ) (projβ (suc n) fzero (u ∷ us))) 
    -- projβ (suc (suc n)) (fsuc x) (u ∷ u' ∷ us) = trans (cong (λ x → x · u' ·s us) Kβ) (projβ (suc n) x (u' ∷ us)) 

    f : Fin (suc n) → Fin n
    f x = proj n x     




--     lookup : ∀{ℓ}{A : Set ℓ}{n : ℕ} → Vec A n → Fin n → A
--     lookup (x ∷ xs) fzero    = x
--     lookup (x ∷ xs) (fsuc i) = lookup xs i
    
--     proj : ∀(k : ℕ) → Fin (suc k) → Tm
--     proj zero fzero = I
--     proj (suc n₁) fzero = B · K · proj  n₁ fzero
--     proj (suc n₁) (fsuc x) = K · proj n₁ x

--     m≤sucm : {m : ℕ} → m < (suc m)
--     m≤sucm {zero} = s≤s z≤n
--     m≤sucm {suc m} = s≤s m≤sucm

--     almost0 : {j : Fin (suc n)} → Fin (suc n) → Tm
--     almost0 {j} x with x ≟ j
--     ... | inr b = fzero
--     ... | inl a = fsuc fzero

--     flatten : ∀{ℓ}{A : Set ℓ}{n : ℕ} → (Fin n → A) → Vec A n
--     flatten {n = zero}  f = []
--     flatten {n = suc n} f = f fzero ∷ flatten {n = n} (f ∘ fsuc)

--     us : {j : Fin (suc n)} → Vec Tm (suc n)
--     us {j} = flatten (almost0 {j})

--   --    projβ : (n : ℕ)(x : Fin n)(us : Vec Tm n) → proj n x ·s us ≡ lookup us x
--   -- projβ (suc zero)    fzero    (u ∷ [])      = Iβ
--   -- projβ (suc (suc n)) fzero    (u ∷ u' ∷ us) = (B · K · (proj (suc n) fzero) · u · u' ·s us)
--   --                                                         ≡⟨ cong (λ z → z · u' ·s us) Bβ ⟩ 
--   --                                               (K · (proj (suc n) fzero · u) · u' ·s us)
--   --                                                         ≡⟨ cong (_·s us) Kβ ⟩ 
--   --                                               (proj (suc n) fzero · u ·s us)
--   --                                                         ≡⟨ projβ (suc n) fzero (u ∷ us) ⟩ 
--   --                                               refl
--   -- projβ (suc (suc n)) (fsuc x) (u ∷ u' ∷ us) =  (K · proj (suc n) x · u · u' ·s us)
--   --                                                       ≡⟨ cong (λ x → x · u' ·s us) Kβ ⟩ 
--   --                                               (proj (suc n) x · u' ·s us)
--   --                                                       ≡⟨ projβ (suc n) x (u' ∷ us) ⟩ 
--   --                                               refl

--     projβ : (n : ℕ)(x : Fin (suc n))(us : Vec Tm (suc n)) → proj n x ·s us ≡ lookup us x
--     projβ zero fzero (u ∷ []) = Iβ
--     projβ (suc n) fzero (u ∷ u' ∷ us) = (B · K · (proj n fzero) · u · u' ·s us)
--                                                   ≡⟨ cong (λ x → (x · u') ·s us) Bβ ⟩ 
--                                         (((K · (proj n fzero · u)) · u') ·s us)
--                                                   ≡⟨ cong (_·s us) Kβ ⟩ 
--                                         ((proj n fzero · u) ·s us)
--                                                   ≡⟨ projβ n fzero (u ∷ us) ⟩ 
--                                         refl

--     projβ (suc n) (fsuc x) (u ∷ u' ∷ us) =  (K · (proj n x)  · u · u' ·s us)
--                                                   ≡⟨ cong (λ x → x · u' ·s us) Kβ ⟩ 
--                                             (proj n x · u' ·s us)
--                                                   ≡⟨ projβ n x (u' ∷ us) ⟩ 
--                                             refl
                                     
--     flattenval : ∀{ℓ}{A : Set ℓ}{n : ℕ}(f : Fin n → A)(x : Fin n) → f x ≡ lookup (flatten f) x 
--     flattenval {n = suc n} f fzero    = refl
--     flattenval {n = suc n} f (fsuc x) = flattenval {n = n} (f ∘ fsuc) x

--     almost0i : ∀{Id j : Fin (suc n)} → Id ≢ j → almost0 {j} Id ≡ fzero
--     almost0i {i}{j} i≠j with Id ≟ j
--     ... | inr b = refl
--     ... | inl a with i≠j a
--     ... | ()

--     almost0j :  ∀{j : Fin (suc n)} → almost0 {j} j ≡ (fsuc fzero)
--     almost0j {j} with j ≟ j
--     ... | inl a = refl
--     ... | inr ¬j with ¬j refl
--     ... | ()
    
--     f : Fin (suc n) → Fin n
--     f x = proj n x 

--     fromPigeon : ∃₂ λ Id j → Id ≢ j × f Id ≡ f j 
--     fromPigeon  = pigeonhole m≤sucm f 
    
--     contra : fzero ≡ fsuc fzero
--     contra with fromPigeon
--     ... | Id , j , i≠j , fi=fj = 
--       fzero
--               ≡⟨ sym (almost0i i≠j )⟩ 
--       almost0 i
--               ≡⟨  flattenval almost0 Id ⟩ 
--       lookup us i
--               ≡⟨ sym (projβ (suc (suc m)) Id (us {j})) ⟩ 
--       ((proj (suc (suc m)) i) ·s us)
--               ≡⟨ cong (λ x → x ·s us ) fi=fj ⟩ 
--       ((proj (suc (suc m)) j) ·s us)
--              ≡⟨ (projβ (suc (suc m)) j (us {j})) ⟩ 
--       lookup us j
--             ≡⟨ sym (flattenval almost0 j) ⟩ 
--       almost0 j
--             ≡⟨ (almost0j {j} ) ⟩ 
--       refl
             
--     bot : ⊥
--     bot with contra
--     bot | ()

-- notbool : (m : Model) → let module m = Model m in m.Tm ≡ (Fin 2) → ⊥
-- notbool m refl = notBoolModel2.bot _·_ K S Kβ Sβ 
--   where
--     open Model m

-- notfinite : (m : Model){n : ℕ} → let module m = Model m in m.Tm ≡ (Fin (suc (suc n))) → ⊥
-- notfinite record { Tm = .(Fin (suc (suc n))) ; _·_ = _·₁_ ; K = K₁ ; S = S₁ ; Kβ = Kβ₁ ; Sβ = Sβ₁ } {n} refl = 
--   notFiniteModel2.bot n _·₁_ K₁ S₁ Kβ₁ Sβ₁ 
      
      