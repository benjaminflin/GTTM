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
        ·-identityₗ : ∀ ρ → one · ρ ≡ ρ 
        ·-identityᵣ : ∀ ρ → ρ · one ≡ ρ 
        0-cancelₗ : ∀ ρ → zero · ρ ≡ ρ
        0-cancelᵣ : ∀ ρ → ρ · zero ≡ ρ
        ·-+-distributiveₗ : ∀ ϕ ρ π → ϕ · (ρ + π) ≡ ϕ · ρ + ϕ · π         
        ·-+-distributiveᵣ : ∀ ϕ ρ π → (ρ + π) · ϕ ≡ ρ · ϕ + π · ϕ
        ≤-+ : ∀ ρ π ϕ → ρ ≤ π → ρ + ϕ ≤ π + ϕ
        ≤-·ₗ : ∀ ρ π ϕ → ρ ≤ π → ϕ · ρ ≤ ϕ · π 
        ≤-·ᵣ : ∀ ρ π ϕ → ρ ≤ π → ρ · ϕ ≤ π · ϕ
```


```agda
module OneClosure where
    record IsPartialSemiring (Q : Set) : Set₁ where 
        infixl 5 _+_ 
        infixl 7 _·_ 
        infix 2 _≤_
        field
            zero : Q
            _+_ : Q → Q → Q
            _·_ : Q → Q → Q 
            _≤_ : Q → Q → Set
            +-identity : ∀ ρ → zero + ρ ≡ ρ 
            +-assoc : ∀ ρ π ϕ → ρ + (π + ϕ) ≡ (ρ + π) + ϕ
            +-comm : ∀ ρ π → ρ + π ≡ π + ρ 
            ·-assoc : ∀ ρ π ϕ → ρ · (π · ϕ) ≡ (ρ · π) · ϕ
            0-cancelₗ : ∀ ρ → zero · ρ ≡ ρ
            0-cancelᵣ : ∀ ρ → ρ · zero ≡ ρ
            ·-+-distributiveₗ : ∀ ϕ ρ π → ϕ · (ρ + π) ≡ ϕ · ρ + ϕ · π         
            ·-+-distributiveᵣ : ∀ ϕ ρ π → (ρ + π) · ϕ ≡ ρ · ϕ + π · ϕ
            ≤-+ : ∀ ρ π ϕ → ρ ≤ π → ρ + ϕ ≤ π + ϕ
            ≤-·ₗ : ∀ ρ π ϕ → ρ ≤ π → ϕ · ρ ≤ ϕ · π 
            ≤-·ᵣ : ∀ ρ π ϕ → ρ ≤ π → ρ · ϕ ≤ π · ϕ
    
    module _ (Q : Set) (P : IsPartialSemiring Q) where
        data OneClosure : Set where 
            q : Q → OneClosure 
            one : OneClosure 

        module P = IsPartialSemiring P

        -- TODO: OneClosure definitions and theorems
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
record Module (R : Set) (M : Set) : Set where 
    field
        zero : R 
        _+_ : M → M → M 
        _·_ : R → M → M 

open import Relation.Binary

module Context (Var : Set) (Quant : Set) (IsQuant : IsQuantity Quant) where 

    open Syntax Var Quant

    data PreContext : Set where
        ∅ₚ : PreContext
        _,_∶_ : PreContext → Var → Type → PreContext

    data Context : Set where 
        ∅ : Context 
        _,[_]_∶_ : Context → Term → Var → Type → Context
    
    ⌊_⌋ : Context → PreContext
    ⌊ ∅ ⌋ = ∅ₚ
    ⌊ Δ ,[ q ] v ∶ t ⌋ = ⌊ Δ ⌋ , v ∶ t 

    infix 10 _·_
    _·_ : Quant → Context → Context
    ρ · ∅ = ∅
    ρ · (Γ ,[ q ] t ∶ T) = (ρ · Γ) ,[ (ρ ₘ) ·ₘ q ] t ∶ T

    infixl 5 _+_
    postulate
        _+_ : Context → Context → Context 

```

```agda

module Rules (Var : Set) (Quant : Set) (IsQuant : IsQuantity Quant) where
    
    open Syntax Var Quant
    open Context Var Quant IsQuant

    private
        variable
            x : Var
            ρ : Quant
            s t a b : Term
            p q r : Term
            A B S T : Type
            Γ Γ₁ Γ₂ Γ₃ : Context 

    open IsQuantity IsQuant using (_≤_; one; zero)

    infix 50 𝟘_
    𝟘_ : Context → Context 
    𝟘_ = zero ·_

    data _⊢_∶_ : Context → Term → Type → Set where
        t-var : 
            -- missing x ∉ ⌊ Γ ⌋
            --------------------------------
            (𝟘 Γ ,[ one ₘ ] x ∶ T) ⊢ ` x ∶ T
        
        t-mult-quant :
            --------------
            𝟘 Γ ⊢ ρ ₘ ∶ mult
        
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


```


