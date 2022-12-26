module GTTM.Quantity where

open import Relation.Binary.PropositionalEquality

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
        0-cancelₗ : ∀ ρ → zero · ρ ≡ zero 
        0-cancelᵣ : ∀ ρ → ρ · zero ≡ zero 
        ·-+-distributiveₗ : ∀ ϕ ρ π → ϕ · (ρ + π) ≡ ϕ · ρ + ϕ · π         
        ·-+-distributiveᵣ : ∀ ϕ ρ π → (ρ + π) · ϕ ≡ ρ · ϕ + π · ϕ
        ≤-refl : ∀ ρ → ρ ≤ ρ
        ≤-irrefl : ∀ ρ π → ρ ≤ π → π ≤ ρ → ρ ≡ π
        ≤-trans : ∀ ρ π ϕ → ρ ≤ π → π ≤ ϕ → ρ ≤ ϕ
        ≤-+ : ∀ ρ π ϕ → ρ ≤ π → ρ + ϕ ≤ π + ϕ
        ≤-·ₗ : ∀ ρ π ϕ → ρ ≤ π → ϕ · ρ ≤ ϕ · π 
        ≤-·ᵣ : ∀ ρ π ϕ → ρ ≤ π → ρ · ϕ ≤ π · ϕ