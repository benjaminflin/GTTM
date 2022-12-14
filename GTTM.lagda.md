# A Usage Aware Graded Dependent Type System with First Class Multiplicites

## Abstract

Graded Type Theory (GTT) by allows resource tracking
by annotation binders with a grade semiring, enabling
a resource tracking of variable usage similar to linear logic.
We describe an extended GTT with first class grades and 
prove progress, preservation, confluence and heap-preservation
properties for this system. This paper is typecheckable as a 
literate agda file.

```agda
module GTTM where 

open import Relation.Binary.PropositionalEquality

```

## Quantities

Quantities are semirings (Q,+,·,0,1) with an ordering relation (≤).

```agda
record IsQuantity (Q : Set) : Set₁ where 
    infixl 5 _+_ 
    infixl 7 _·_ 
    infix 2 _≤_
    field
        zero : Q
        one : Q
        _+_ : Q → Q → Q
        _·_ : Q → Q → Q 
        _≤_ : Q → Q → Set
        +-identity : ∀ ρ → zero + ρ ≡ ρ 
        +-assoc : ∀ ρ π ϕ → ρ + (π + ϕ) ≡ (ρ + π) + ϕ
        +-comm : ∀ ρ π → ρ + π ≡ π + ρ 
        ·-assoc : ∀ ρ π ϕ → ρ · (π · ϕ) ≡ (ρ · π) · ϕ
        -- Are these actually necessary for the theory? 
        -- It would be nice if quantities could have 0 = 1 in a non-trivial way
        -- ·-identityₗ : ∀ ρ → one · ρ ≡ ρ 
        -- ·-identityᵣ : ∀ ρ → ρ · one ≡ ρ 
        0-cancelₗ : ∀ ρ → zero · ρ ≡ zero 
        0-cancelᵣ : ∀ ρ → ρ · zero ≡ zero 
        ·-+-distributiveₗ : ∀ ϕ ρ π → ϕ · (ρ + π) ≡ ϕ · ρ + ϕ · π         
        ·-+-distributiveᵣ : ∀ ϕ ρ π → (ρ + π) · ϕ ≡ ρ · ϕ + π · ϕ
        ≤-refl : ∀ ρ → ρ ≤ ρ
        -- might also not be needed
        -- ≤-irrefl : ∀ ρ π → ρ ≤ π → π ≤ ρ → ρ ≡ π
        ≤-trans : ∀ ρ π ϕ → ρ ≤ π → π ≤ ϕ → ρ ≤ ϕ
        ≤-+ : ∀ ρ π ϕ → ρ ≤ π → ρ + ϕ ≤ π + ϕ
        ≤-·ₗ : ∀ ρ π ϕ → ρ ≤ π → ϕ · ρ ≤ ϕ · π 
        ≤-·ᵣ : ∀ ρ π ϕ → ρ ≤ π → ρ · ϕ ≤ π · ϕ
```


```agda
module Syntax (Var : Set) (Quant : Set) where 

    data Term : Set 

    Type : Set
    Type = Term

    data Term where
        ⋆ : Type 
        mult : Type 
        _+ₘ_ : Term → Term → Term
        _·ₘ_ : Term → Term → Term
        _ₘ : Quant → Term 
        ⦅[_]_∶_⦆⇒_ : Term → Var → Type → Type → Type 
        ƛ[_]_∶_⇒_ : Term → Var → Type → Term → Term 
        `_ : Var → Term 
        _∙_ : Term → Term → Term
    
```

```agda
open import Relation.Binary

module Context (Var : Set) (Quant : Set) (IsQuant : IsQuantity Quant) where 

    open Syntax Var Quant
    open import Data.Product

    data PreContext : Set where
        ∅ₚ : PreContext
        _,_∶_ : PreContext → Var → Type → PreContext

    data Context : Set where 
        ∅ : Context 
        _,[_]_∶_ : Context → Term → Var → Type → Context

    private
        variable
            x y : Var
            p q r s t : Term
            S T A B : Type
            Γ Γ₁ Γ₂ Δ : Context
            Γₚ Δₚ ⌊Γ₁⌋ ⌊Γ₂⌋ : PreContext
            ρ ϕ : Quant

    ⌊_⌋ : Context → PreContext
    ⌊ ∅ ⌋ = ∅ₚ
    ⌊ Δ ,[ q ] v ∶ t ⌋ = ⌊ Δ ⌋ , v ∶ t 

    data HasPreContext : Context → PreContext → Set where 
        has-∅ₚ : HasPreContext ∅ ∅ₚ
        has-, : HasPreContext Γ Γₚ → HasPreContext (Γ ,[ p ] x ∶ A) (Γₚ , x ∶ A)


    hasPreContext : ∀ Γ → HasPreContext Γ ⌊ Γ ⌋
    hasPreContext ∅ = has-∅ₚ
    hasPreContext (Γ ,[ p ] x ∶ A) = has-, (hasPreContext Γ)

    preContextInjective : (⌊Γ₁⌋ , x ∶ A) ≡ (⌊Γ₂⌋ , y ∶ B) → ⌊Γ₁⌋ ≡ ⌊Γ₂⌋
    preContextInjective refl = refl 

    preContextLemma : (⌊Γ₁⌋ , x ∶ A) ≡ (⌊Γ₂⌋ , y ∶ B) → x ≡ y × A ≡ B 
    preContextLemma refl = refl , refl

    samePreContext : (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) → ∃[ Γₚ ] HasPreContext Γ₁ Γₚ × HasPreContext Γ₂ Γₚ      
    samePreContext {Γ₁ = ∅} {Γ₂ = ∅} Γ₁₂-≡ = ∅ₚ , (has-∅ₚ , has-∅ₚ)
    samePreContext {Γ₁ = Γ₁ ,[ p ] x ∶ A} {Γ₂ = Γ₂ ,[ q ] y ∶ B} Γ₁₂-≡ 
        rewrite preContextInjective Γ₁₂-≡ 
        with (refl , refl) ← preContextLemma Γ₁₂-≡ 
        with (Γₚ , hpc₁ , hpc₂) ← samePreContext (preContextInjective Γ₁₂-≡) 
        = (Γₚ , x ∶ A) , (has-, hpc₁) , (has-, hpc₂) 

    infix 10 _·_
    _·_ : Term → Context → Context
    p · ∅ = ∅
    p · (Γ ,[ q ] t ∶ T) = (p · Γ) ,[ p ·ₘ q ] t ∶ T


    module Qu = IsQuantity IsQuant
    open IsQuantity IsQuant using (zero)

    infix 50 𝟘_
    𝟘_ : Context → Context 
    𝟘 ∅ = ∅
    𝟘 (Γ ,[ p ] x ∶ T) = 𝟘 Γ ,[ zero ₘ ] x ∶ T

    𝟘-idempotent : ∀ Γ → 𝟘 (𝟘 Γ) ≡ 𝟘 Γ
    𝟘-idempotent ∅ = refl
    𝟘-idempotent (Γ ,[ p ] x ∶ T) = cong (_,[ zero ₘ ] x ∶ T) (𝟘-idempotent Γ)

    _++_ : Context → Context → Context
    Γ₁ ++ ∅ = Γ₁
    Γ₁ ++ (Γ₂ ,[ p ] x ∶ A) = (Γ₁ ++ Γ₂) ,[ p ] x ∶ A

    infixl 5 _++_

    _+_[_] : (Γ₁ : Context) → (Γ₂ : Context) → (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) → Context 
    Γ₁ + Γ₂ [ Γ₁₂-≡ ] = go Γ₁ Γ₂ (samePreContext Γ₁₂-≡)
        where
        go : (Γ₁ : Context) → (Γ₂ : Context) → ∃[ Γₚ ] HasPreContext Γ₁ Γₚ × HasPreContext Γ₂ Γₚ → Context  
        go .∅ .∅ (.∅ₚ , has-∅ₚ , has-∅ₚ) = ∅
        go (Γ₁ ,[ p ] x ∶ A) (Γ₂ ,[ q ] x ∶ A) ((Γₚ , _ ∶ _) , (has-, hpc₁) , (has-, hpc₂)) 
            = go Γ₁ Γ₂ (Γₚ , hpc₁ , hpc₂) ,[ p +ₘ q ] x ∶ A

    infix 2 _≤_ 
    data _≤_ : Context → Context → Set where
        ≤-∅ : ∅ ≤ ∅ 
        ≤-, : Γ₁ ≤ Γ₂ → ρ Qu.≤ ϕ → Γ₁ ,[ ρ ₘ ] x ∶ A ≤ Γ₁ ,[ ϕ ₘ ] x ∶ A

    open import Data.List hiding (_++_)
    dom : Context → List Var  
    dom ∅ = []
    dom (Γ ,[ _ ] x ∶ _) = x ∷ dom Γ

    data _∶_∈_ : Var → Term → Context → Set where
        here : x ∶ A ∈ (Γ ,[ p ] x ∶ A)
        there : x ∶ A ∈ Γ → x ≢ y → x ∶ A ∈ (Γ ,[ p ] y ∶ B)

    open import Data.List.Membership.Propositional 
    open import Relation.Nullary.Negation
    open import Data.List.Relation.Unary.Any renaming (here to hereₗ ; there to thereₗ)
    open import Data.Empty

    Γ-∈-≡ : x ∶ A ∈ Γ₁ → x ∶ B ∈ Γ₂ → Γ₁ ≡ Γ₂ → A ≡ B 
    Γ-∈-≡ here here refl = refl
    Γ-∈-≡ here (there ∈Γ₂ x≠x) refl = ⊥-elim (x≠x refl)
    Γ-∈-≡ (there ∈Γ₁ x≠x) here refl = ⊥-elim (x≠x refl)
    Γ-∈-≡ (there ∈Γ₁ x≠y) (there ∈Γ₂ y≠z) refl = Γ-∈-≡ ∈Γ₁ ∈Γ₂ refl 

    Γ-++ : x ∉ dom Γ₂ → x ∶ A ∈ ((Γ₁ ,[ p ] x ∶ A) ++ Γ₂)
    Γ-++ {Γ₂ = ∅} x∉Γ₂ = here
    Γ-++ {Γ₂ = Γ₂ ,[ q ] y ∶ B} x∉Γ₂ = there (Γ-++ (∈-cons x∉Γ₂)) (∈-≢ x∉Γ₂)
        where
        ∈-cons : ∀ {x y} {xs : List Var} → x ∉ y ∷ xs → x ∉ xs 
        ∈-cons ∉yxs (hereₗ px) = ∉yxs (thereₗ (hereₗ px))
        ∈-cons ∉yxs (thereₗ ∈xs) = ∉yxs (thereₗ (thereₗ ∈xs)) 

        ∈-≢ : ∀ {x y} {xs : List Var} → x ∉ y ∷ xs → x ≢ y 
        ∈-≢ ∉yxs x=y = ∉yxs (hereₗ x=y)
    
```

```agda
open import Relation.Binary.Definitions

module Substitution (Var : Set) (Quant : Set) (IsQuant : IsQuantity Quant) (_≟_ : DecidableEquality Var) where
    open Syntax Var Quant
    open Context Var Quant IsQuant 

    open import Relation.Nullary using (does) 
    open import Data.Bool using (if_then_else_)

    _[_/_] : Term → Term → Var → Term
    ⋆ [ a / x ] = ⋆
    mult [ a / x ] = mult
    (p +ₘ q) [ a / x ] = (p [ a / x ]) +ₘ (q [ a / x ])
    (p ·ₘ q) [ a / x ] = (p [ a / x ]) ·ₘ (q [ a / x ])
    (q ₘ) [ a / x ] = q ₘ
    (⦅[ p ] y ∶ A ⦆⇒ B) [ a / x ] = 
        if does (x ≟ y) then 
            ⦅[ p [ a / x ] ] y ∶ (A [ a / x ]) ⦆⇒ B 
        else 
            ⦅[ p [ a / x ] ] y ∶ (A [ a / x ]) ⦆⇒ (B [ a / x ])
    (ƛ[ p ] y ∶ A ⇒ B) [ a / x ] = 
        if does (x ≟ y) then 
            ƛ[ p [ a / x ] ] y ∶ (A [ a / x ]) ⇒ B 
        else 
            (ƛ[ p [ a / x ] ] y ∶ (A [ a / x ]) ⇒ (B [ a / x ]))
    (` y) [ a / x ] = if does (x ≟ y) then a else ` y 
    (s ∙ t) [ a / x ] = (s [ a / x ]) ∙ (t [ a / x ])

    _⟦_/_⟧ : Context → Term → Var → Context
    ∅ ⟦ a / x ⟧ = ∅
    (Γ ,[ p ] y ∶ A) ⟦ a / x ⟧ = {!   !} -- if does (x ≟ y) then Γ ,[ p ] y : A else {!   !}

```

```agda

module Rules (Var : Set) (_≟_ : DecidableEquality Var) (Quant : Set) (IsQuant : IsQuantity Quant) where
    
    open Syntax Var Quant
    open Context Var Quant IsQuant
    open Substitution Var Quant IsQuant _≟_ 

    private
        variable
            x : Var
            ρ : Quant
            s t a b : Term
            p q r : Term
            A B S T R : Type
            Γ Γ₁ Γ₂ Γ₃ : Context 

    open IsQuantity IsQuant using (one; zero)

    data _⊢_∶_ : Context → Term → Type → Set where
        t-var : 
            (𝟘Γ : Γ ≡ 𝟘 Γ) →
            ------------------------------
            (Γ ,[ one ₘ ] x ∶ T) ⊢ ` x ∶ T

        t-mult-type :
            ------------
            ∅ ⊢ mult ∶ ⋆

        t-type-type : 
            ---------
            ∅ ⊢ ⋆ ∶ ⋆  

        t-mult-quant :
            --------------
            ∅ ⊢ ρ ₘ ∶ mult
        
        t-mult-+ :
            (⊢p : Γ₁ ⊢ p ∶ mult) →
            (⊢q : Γ₂ ⊢ q ∶ mult) →
            (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
            (Γ-split : (Γ₁ + Γ₂ [ Γ₁₂-≡ ]) ≡ Γ) →
            -----------------
            Γ ⊢ p +ₘ q ∶ mult

        t-mult-· :
            (⊢p : Γ₁ ⊢ p ∶ mult) →
            (⊢q : Γ₂ ⊢ q ∶ mult) →
            (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
            (Γ-split : (Γ₁ + Γ₂ [ Γ₁₂-≡ ]) ≡ Γ) →
            -----------------
            Γ ⊢ p ·ₘ q ∶ mult 

        t-lam : 
            (⊢a : (Γ₁ ,[ p ] x ∶ A) ⊢ a ∶ B) →
            (⊢p : Γ₂ ⊢ p ∶ mult) → 
            (⊢A : Γ₃ ⊢ A ∶ ⋆) →
            (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
            (Γ₁₃-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₃ ⌋) →
            --------------------------------------------
            Γ₁ ⊢ (ƛ[ p ] x ∶ A ⇒ a) ∶ (⦅[ p ] x ∶ A ⦆⇒ B)

        t-pi :
            (⊢p : Γ₁ ⊢ p ∶ mult) →
            (⊢A : Γ₂ ⊢ A ∶ ⋆) →
            (⊢B : (Γ₃ ,[ p ] x ∶ A) ⊢ B ∶ ⋆) →
            (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
            (Γ₁₃-≡ : ⌊ Γ₁ + Γ₂ [ Γ₁₂-≡ ] ⌋ ≡ ⌊ Γ₃ ⌋) →
            (Γ-split : ((Γ₁ + Γ₂ [ Γ₁₂-≡ ]) + Γ₃ [ Γ₁₃-≡ ]) ≡ Γ) → 
            ---------------------------- 
            Γ ⊢ (⦅[ p ] x ∶ A ⦆⇒ B) ∶ ⋆ 
        
        t-app :
            (⊢s : Γ₁ ⊢ s ∶ (⦅[ p ] x ∶ A ⦆⇒ B)) →
            (⊢t : Γ₂ ⊢ t ∶ A) →
            (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ p · Γ₂ ⌋) →
            (Γ-split : (Γ₁ + (p · Γ₂) [ Γ₁₂-≡ ]) ≡ Γ) →
            (R-conv : R ≡ (B [ t / x ])) →
            ------------------------------
            Γ ⊢ (s ∙ t) ∶ R 
        
        t-sub :
            (⊢a : Γ₁ ⊢ a ∶ A) → 
            (Γ-≤ : Γ₁ ≤ Γ₂) → 
            (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
            ---------------------------
            Γ₂ ⊢ a ∶ A 
        
        t-weak :
            (⊢b : Γ₁ ⊢ b ∶ B) →
            (⊢A : Γ₂ ⊢ A ∶ ⋆) →
            ------------------------------
            (Γ₁ ,[ zero ₘ ] x ∶ A) ⊢ b ∶ B

```


```agda
module Normalization (Var : Set) (_≟_ : DecidableEquality Var) (Quant : Set) (IsQuant : IsQuantity Quant) where

    open Syntax Var Quant
    open Context Var Quant IsQuant
    open Substitution Var Quant IsQuant _≟_ 
    open Rules Var _≟_ Quant IsQuant 
    
    private
        variable
            x y : Var
            p p′ q q′ r s t u v a b c : Term
            S T A B : Type
            Γ Γ₁ Γ₂ Δ : Context

    module Q = IsQuantity IsQuant
    
    infix 2 _⟶_
    data _⟶_ : Term → Term → Set where 
        β-reduce : ∀ p x A a b → (ƛ[ p ] x ∶ A ⇒ a) ∙ b ⟶ a [ b / x ]
        +-known : ∀ ρ π → ((ρ ₘ) +ₘ (π ₘ)) ⟶ (ρ Q.+ π) ₘ
        ·-known : ∀ ρ π → ((ρ ₘ) ·ₘ (π ₘ)) ⟶ (ρ Q.· π) ₘ
        +-0ₗ : ∀ p → (Q.zero ₘ) +ₘ p ⟶ p  
        +-0ᵣ : ∀ p → p +ₘ (Q.zero ₘ) ⟶ p  
        ·-0ₗ : ∀ p → (Q.zero ₘ) ·ₘ p ⟶ (Q.zero ₘ)  
        ·-0ᵣ : ∀ p → p ·ₘ (Q.zero ₘ) ⟶ (Q.zero ₘ)

    infix 2 _▸_
    data _▸_ : Term → Term → Set where 
        refl-▸ : s ▸ s 
        trans-▸ : a ▸ b → (b⟶c : b ⟶ c) → a ▸ c   

    trans-▸′ : a ▸ b → b ▸ c → a ▸ c
    trans-▸′ a▸b refl-▸ = a▸b 
    trans-▸′ a▸b (trans-▸ b▸c b⟶c) = trans-▸ (trans-▸′ a▸b b▸c) b⟶c


    -- admissible-subst {a = ⋆} _ (t-type-type _) _ = t-type-type refl
    -- admissible-subst {a = mult} _ (t-mult-type _) _ = t-mult-type refl
    -- admissible-subst {a = p +ₘ q} x∈Γ (t-mult-+ ⊢p ⊢q ⌊Γ⌋-≡ Γ-split) ⊢b 
    --     with (r , s , x∈Γ₁ , x∈Γ₂ , _) ← context-split-lemma x∈Γ Γ-split ⌊Γ⌋-≡ = 
    --     t-mult-+ (admissible-subst x∈Γ₁ ⊢p ⊢b) (admissible-subst x∈Γ₂ ⊢q ⊢b) refl refl
    -- admissible-subst {a = p ·ₘ q} x∈Γ (t-mult-· ⊢p ⊢q ⌊Γ⌋-≡ Γ-split) ⊢b 
    --     with (r , s , x∈Γ₁ , x∈Γ₂ , _) ← context-split-lemma x∈Γ Γ-split ⌊Γ⌋-≡ =
    --     t-mult-· (admissible-subst x∈Γ₁ ⊢p ⊢b) (admissible-subst x∈Γ₂ ⊢q ⊢b) refl refl 
    -- admissible-subst {a = ρ ₘ} x∈Γ t-mult-quant ⊢b = t-mult-quant
    -- admissible-subst {x = x} {a = ⦅[ p ] y ∶ S ⦆⇒ T} x∈Γ (t-pi {Γ₁ = Γ₁} {Γ₂ = Γ₂} {Γ₃ = Γ₃} ⊢p ⊢A ⊢B ⌊Γ⌋₁₂-≡ ⌊Γ⌋₁₃-≡ Γ-split) ⊢b with x ≟ y 
    -- ... | yes refl rewrite +-assoc Γ₁ Γ₂ Γ₃ = 
    --     let ⌊Γ⌋₂₃-≡ = trans (sym ⌊Γ⌋₁₂-≡) ⌊Γ⌋₁₃-≡ in  
    --     let ⌊Γ₂+Γ₃⌋≡⌊Γ₂⌋ = proj₁ (precontext-absorption-+ ⌊Γ⌋₂₃-≡) in
    --     let (r , s , x∈Γ₁ , x∈Γ₂₃ , _) = context-split-lemma {Γ₁ = Γ₁} {Γ₂ = Γ₂ + Γ₃} x∈Γ Γ-split (sym (trans ⌊Γ₂+Γ₃⌋≡⌊Γ₂⌋ (sym ⌊Γ⌋₁₂-≡))) in 
    --     let ⊢p[b/y] = admissible-subst x∈Γ₁ ⊢p ⊢b in    
    --     {!   !} -- t-pi {!   !} {!   !} {!   !} {!   !} {!   !}
    -- ... | no _ = {!   !}
    -- admissible-subst {a = Syntax.ƛ[ a ] x ∶ x₁ ⇒ a₁} x∈Γ ⊢a ⊢b = {!   !}
    -- admissible-subst {x = x} {a = Syntax.` y} x∈Γ ⊢a ⊢b with x ≟ y 
    -- ... | yes refl rewrite x∈Γ-lemma x∈Γ ⊢a = ⊢b
    -- ... | no _ = {! ⊢a  !}
    -- admissible-subst {a = s Syntax.∙ t} x∈Γ ⊢a ⊢b = {!   !}

```

```agda
module Admissibility (Var : Set) (_≟_ : DecidableEquality Var) (Quant : Set) (IsQuant : IsQuantity Quant) where

    open Syntax Var Quant
    open Context Var Quant IsQuant
    open Substitution Var Quant IsQuant _≟_ 
    open Rules Var _≟_ Quant IsQuant 

    private
        variable
            x y : Var
            p p′ q q′ r s t u v a b c : Term
            S T A B : Type
            Γ Γ₁ Γ₂ Δ : Context
    
    open import Relation.Nullary
    open import Data.Product
    open import Data.Empty

    open import Data.List.Membership.Propositional 
 
    module Q = IsQuantity IsQuant



    subst-admissible-var-lemma : x ∉ dom Γ₂ → Δ ≡ ((Γ₁ ,[ p ] x ∶ A) ++ Γ₂) → Δ ⊢ ` x ∶ B → B ≡ A
    subst-admissible-var-lemma ∉Γ₂ Δ-≡ (t-var 𝟘Γ) = Γ-∈-≡ here (Γ-++ ∉Γ₂) Δ-≡
    subst-admissible-var-lemma ∉Γ₂ Δ-≡ (t-sub {Γ₁ = Γ} {Γ₂ = Γ′} ⊢x Γ-≤ Γ₁₂-≡) = subst-admissible-var-lemma {!   !} {!   !} ⊢x
    subst-admissible-var-lemma ∉Γ₂ Δ-≡ (t-weak {Γ₁ = Γ} {Γ₂ = Γ′} ⊢b ⊢A) = {!   !}

    subst-admissible : (Γ-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ p · Γ ⌋) → 
                (Δ ≡ (Γ₁ ,[ p ] x ∶ A ++ Γ₂)) →
                Γ ⊢ a ∶ A → 
                Δ ⊢ b ∶ B → 
                (Γ₁ + (p · Γ) [ Γ-≡ ] ++ Γ₂) ⊢ (b [ a / x ]) ∶ (B [ a / x ])
    subst-admissible {x = x} {b = b} Γ-≡ Δ-≡ ⊢a (Rules.t-var {x = y} 𝟘Γ) with (x ≟ y) 
    ... | yes refl = {!   !} -- need to show: A ≡ B ≡ B [ a / x ], Γ₂ = 𝟘Γ₂, p = 0, then can construct result by weakening 
    ... | no contra = {!   !} -- need to show: p = 0 (since x is not used), and then show ability to carve out x from context
    subst-admissible Γ-≡ Δ-≡ ⊢a Rules.t-mult-type = {!   !}
    subst-admissible Γ-≡ Δ-≡ ⊢a Rules.t-type-type = {!   !}
    subst-admissible Γ-≡ Δ-≡ ⊢a Rules.t-mult-quant = {!   !}
    subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-mult-+ ⊢b ⊢b₁ Γ₁₂-≡ Γ-split) = {!   !}
    subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-mult-· ⊢b ⊢b₁ Γ₁₂-≡ Γ-split) = {!   !}
    subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-lam ⊢b ⊢b₁ ⊢b₂ Γ₁₂-≡ Γ₁₃-≡) = {!   !}
    subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-pi ⊢b ⊢b₁ ⊢b₂ Γ₁₂-≡ Γ₁₃-≡ Γ-split) = {!   !}
    subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-app ⊢b ⊢b₁ Γ₁₂-≡ Γ-split R-conv) = {!   !}
    subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-sub ⊢b Γ-≤ Γ₁₂-≡) = {!   !}
    subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-weak ⊢b ⊢b₁) = {!   !}

    -- x∈Γ-lemma : [ p ] x ∶ B ∈ Γ → Γ ⊢ ` x ∶ A → A ≡ B     
    -- x∈Γ-lemma Context.here (Rules.t-var (Context.here₀ x)) = refl
    -- x∈Γ-lemma Context.here (Rules.t-var (Context.there₀ x∈₀Γ x≠x)) with () ← x≠x refl
    -- x∈Γ-lemma (Context.there x∈Γ x) ⊢x = x∈Γ-lemma x∈Γ {!   !}

    -- admissible-subst : [ p ] x ∶ B ∈ Γ → Γ ⊢ a ∶ A → ∅ ⊢ b ∶ B → Γ ⊢ a [ b / x ] ∶ A
    -- admissible-subst {a = ⋆} x∈Γ (Rules.t-type-type 𝟘Γ) ⊢b = t-type-type 𝟘Γ
    -- admissible-subst {a = mult} x∈Γ ⊢a ⊢b = ⊢a
    -- admissible-subst {a = p +ₘ q} x∈Γ (t-mult-+ ⊢p ⊢q ⌊Γ⌋-≡ Γ-split) ⊢b 
    --     with (r , s , x∈Γ₁ , x∈Γ₂ , _) ← context-split-lemma x∈Γ Γ-split ⌊Γ⌋-≡ =
    --     t-mult-+ (admissible-subst x∈Γ₁ ⊢p ⊢b) (admissible-subst x∈Γ₂ ⊢q ⊢b) ⌊Γ⌋-≡ Γ-split
    -- admissible-subst {a = p ·ₘ q} x∈Γ (t-mult-· ⊢p ⊢q ⌊Γ⌋-≡ Γ-split) ⊢b 
    --     with (r , s , x∈Γ₁ , x∈Γ₂ , _) ← context-split-lemma x∈Γ Γ-split ⌊Γ⌋-≡ =
    --     t-mult-· (admissible-subst x∈Γ₁ ⊢p ⊢b) (admissible-subst x∈Γ₂ ⊢q ⊢b) ⌊Γ⌋-≡ Γ-split 
    -- admissible-subst {a = ρ ₘ} x∈Γ (t-mult-quant 𝟘Γ) ⊢b = t-mult-quant 𝟘Γ
    -- admissible-subst {a = ⦅[ a ] x ∶ S ⦆⇒ T} x∈Γ ⊢a ⊢b = {!   !}
    -- admissible-subst {a = ƛ[ a ] x ∶ S ⇒ b} x∈Γ ⊢a ⊢b = {!   !}
    -- admissible-subst {x = x} {a = ` y} x∈Γ ⊢a ⊢b with x ≟ y 
    -- ... | yes refl rewrite x∈Γ-lemma x∈Γ ⊢a = {!   !} -- need to weaken ∅ → Γ
    -- ... | no _ = ⊢a
    -- admissible-subst {a = s ∙ t} x∈Γ ⊢a ⊢b = {!   !}



    -- rename : 
    --     (∀ {x p A} → [ p ] x ∶ A ∈₀ Γ → [ p ] x ∶ A ∈₀ Δ) →
    --     (∀ {Γ Δ} → 𝟘 Γ ≡ Γ → 𝟘 Δ ≡ Δ) → 
    --     ∀ {t A} → Γ ⊢ t ∶ A → Δ ⊢ t ∶ A
    -- rename μ τ (t-var ∈₀Γ) = t-var (μ ∈₀Γ)
    -- rename {Γ = Γ} {Δ = Δ} μ τ t-mult-type rewrite sym (τ {Γ = 𝟘 Γ} {Δ = Δ} (𝟘-idempotent Γ)) = t-mult-type 
    -- rename μ τ Rules.t-type-type = {!   !}
    -- rename μ τ Rules.t-mult-quant = {!   !}
    -- rename μ τ (Rules.t-mult-+ ⊢t ⊢t₁ x) = {!   !}
    -- rename μ τ (Rules.t-mult-· ⊢t ⊢t₁ x) = {!   !}
    -- rename μ τ (Rules.t-lam ⊢t ⊢t₁ ⊢t₂ x x₁) = {!   !}
    -- rename μ τ (Rules.t-pi ⊢t ⊢t₁ ⊢t₂ x x₁) = {!   !}
    -- rename μ τ (Rules.t-app ⊢t ⊢t₁ x) = {!   !}

```
 
