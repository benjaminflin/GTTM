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
            Γ Δ : Context

    data [_]_∶_∈_ : Term → Var → Type → Context → Set where
        here : [ p ] x ∶ T ∈ (Γ ,[ p ] x ∶ T)
        there : [ p ] x ∶ T ∈ Γ → x ≢ y → [ p ] x ∶ T ∈ (Γ ,[ q ] y ∶ S)

    ⌊_⌋ : Context → PreContext
    ⌊ ∅ ⌋ = ∅ₚ
    ⌊ Δ ,[ q ] v ∶ t ⌋ = ⌊ Δ ⌋ , v ∶ t 

    infix 10 _·_
    _·_ : Term → Context → Context
    p · ∅ = ∅
    p · (Γ ,[ q ] t ∶ T) = (p · Γ) ,[ p ·ₘ q ] t ∶ T

    open IsQuantity IsQuant using (zero)

    infix 50 𝟘_
    𝟘_ : Context → Context 
    𝟘_ = zero ₘ ·_

    data [_]_∶_∈₀_ : Term → Var → Type → Context → Set where
        here₀ : [ p ] x ∶ T ∈₀ (𝟘 Γ ,[ p ] x ∶ T)
        there₀ : [ p ] x ∶ T ∈₀ Γ → x ≢ y → [ p ] x ∶ T ∈₀ (Γ ,[ zero ₘ ] y ∶ S)

    infixl 5 _+_
    postulate
        _+_ : Context → Context → Context 

```

```agda
open import Relation.Binary.Definitions

module Substitution (Var : Set) (Quant : Set) (_≟_ : DecidableEquality Var) where
    open Syntax Var Quant

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

```

```agda

module Rules (Var : Set) (_≟_ : DecidableEquality Var) (Quant : Set) (IsQuant : IsQuantity Quant) where
    
    open Syntax Var Quant
    open Context Var Quant IsQuant
    open Substitution Var Quant _≟_ 

    private
        variable
            x : Var
            ρ : Quant
            s t a b : Term
            p q r : Term
            A B S T : Type
            Γ Γ₁ Γ₂ Γ₃ : Context 

    open IsQuantity IsQuant using (_≤_; one; zero)

    data _⊢_∶_ : Context → Term → Type → Set where
        t-var : 
            [ one ₘ ] x ∶ T ∈₀ Γ →
            ----------------------
            Γ ⊢ ` x ∶ T

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
            Γ₁ ⊢ p ∶ mult →
            Γ₂ ⊢ q ∶ mult →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            -----------------
            (Γ₁ + Γ₂) ⊢ p +ₘ q ∶ mult

        t-mult-· :
            Γ₁ ⊢ p ∶ mult →
            Γ₂ ⊢ q ∶ mult →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            -----------------
            (Γ₁ + Γ₂) ⊢ p ·ₘ q ∶ mult 

        t-lam : 
            (Γ₁ ,[ p ] x ∶ A) ⊢ a ∶ B →
            Γ₂ ⊢ p ∶ mult → 
            Γ₃ ⊢ A ∶ ⋆ →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₃ ⌋ →
            -------------------------------------------
            Γ₁ ⊢ (ƛ[ p ] x ∶ A ⇒ a) ∶ (⦅[ p ] x ∶ A ⦆⇒ B)

        t-pi :
            Γ₁ ⊢ p ∶ mult →
            Γ₂ ⊢ A ∶ ⋆ →
            (Γ₃ ,[ p ] x ∶ A) ⊢ B ∶ ⋆ →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₃ ⌋ →
            ---------------------------- 
            (Γ₁ + Γ₂ + Γ₃) ⊢ (⦅[ p ] x ∶ A ⦆⇒ B) ∶ ⋆ 
        
        t-app :
            Γ₁ ⊢ s ∶ (⦅[ p ] x ∶ A ⦆⇒ B) →
            Γ₂ ⊢ t ∶ A →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            ------------------------------
            (Γ₁ + p · Γ₂) ⊢ (s ∙ t) ∶ (B [ t / x ])

```


 