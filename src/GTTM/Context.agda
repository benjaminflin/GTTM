open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import GTTM.Quantity


module GTTM.Context (Var : Set) (Quant : Set) (IsQuant : IsQuantity Quant) where 
    open import GTTM.Syntax Var Quant
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
            Γ Γ₁ Γ₂ Γ₃ Δ : Context
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

    hpc→≡ : HasPreContext Γ Γₚ → ⌊ Γ ⌋ ≡ Γₚ 
    hpc→≡  has-∅ₚ = refl
    hpc→≡ (has-, {x = x} {A = A} hpc) = cong (_, x ∶ A) (hpc→≡ hpc) 

    ≡→hpc : ⌊ Γ ⌋ ≡ Γₚ → HasPreContext Γ Γₚ    
    ≡→hpc {Γ = Γ} refl = hasPreContext Γ

    preContextInjective : (⌊Γ₁⌋ , x ∶ A) ≡ (⌊Γ₂⌋ , y ∶ B) → ⌊Γ₁⌋ ≡ ⌊Γ₂⌋
    preContextInjective refl = refl 

    preContextLemma : (⌊Γ₁⌋ , x ∶ A) ≡ (⌊Γ₂⌋ , y ∶ B) → x ≡ y × A ≡ B 
    preContextLemma refl = refl , refl

    samePreContext : (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) → HasPreContext Γ₁ ⌊ Γ₂ ⌋
    samePreContext {Γ₁ = Γ₁} {Γ₂ = Γ₂} Γ₁₂-≡ = subst (HasPreContext Γ₁) Γ₁₂-≡ (hasPreContext Γ₁) 

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
    Γ₁ + Γ₂ [ Γ₁₂-≡ ] = go Γ₁ Γ₂ (samePreContext Γ₁₂-≡) (hasPreContext Γ₂) 
        where
        go : (Γ₁ : Context) → (Γ₂ : Context) → HasPreContext Γ₁ ⌊ Γ₂ ⌋ →  HasPreContext Γ₂ ⌊ Γ₂ ⌋ → Context  
        go ∅ ∅ has-∅ₚ has-∅ₚ = ∅
        go ∅ (Γ₂ ,[ x ] x₁ ∶ x₂) () hpc₂
        go (Γ₁ ,[ x ] x₁ ∶ x₂) ∅ () hpc₂
        go (Γ₁ ,[ p ] x ∶ A) (Γ₂ ,[ q ] x ∶ A) (has-, hpc₁) (has-, hpc₂) = go Γ₁ Γ₂ hpc₁ hpc₂  

    infix 2 _≤_ 
    data _≤_ : Context → Context → Set where
        ≤-∅ : ∅ ≤ ∅ 
        ≤-, : Γ₁ ≤ Γ₂ → ρ Qu.≤ ϕ → Γ₁ ,[ ρ ₘ ] x ∶ A ≤ Γ₂ ,[ ϕ ₘ ] x ∶ A

    open import Data.List hiding (_++_)
    dom : Context → List Var  
    dom ∅ = []
    dom (Γ ,[ _ ] x ∶ _) = x ∷ dom Γ

    data _∶_∈_ : Var → Term → Context → Set where
        here : x ∶ A ∈ (Γ ,[ p ] x ∶ A)
        there : x ∶ A ∈ Γ → x ≢ y → x ∶ A ∈ (Γ ,[ p ] y ∶ B)

    data _∶_∈[_]_ : Var → Term → Term → Context → Set where
        here′ : x ∶ A ∈[ p ] (Γ ,[ p ] x ∶ A)
        there′ : x ∶ A ∈[ p ] Γ → x ≢ y → x ∶ A ∈[ p ] (Γ ,[ q ] y ∶ B)

    ∈-respects-≤ : (x ∶ A ∈ Γ₁) → Γ₁ ≤ Γ₂ → (x ∶ A ∈ Γ₂)
    ∈-respects-≤ here (≤-, ≤-Γ ρ≤ϕ) = here
    ∈-respects-≤ (there ∈Γ₁ x≠y) (≤-, ≤-Γ x) = there (∈-respects-≤ ∈Γ₁ ≤-Γ) x≠y

    ∈-respects-≥ : (x ∶ A ∈ Γ₁) → Γ₂ ≤ Γ₁ → (x ∶ A ∈ Γ₂)
    ∈-respects-≥ here (≤-, ≤-Γ ρ≤ϕ) = here
    ∈-respects-≥ (there ∈Γ₁ x≠y) (≤-, ≤-Γ x) = there (∈-respects-≥ ∈Γ₁ ≤-Γ) x≠y 

    -- ∈-respects-≥ : (x ∶ A ∈[ p ] Γ₁) → Γ₂ ≤ Γ₁ → ∃[ ϕ ] (x ∶ A ∈[ ϕ ₘ ] Γ₂) × ϕ ₘ ≤ p  


    open import Data.List.Membership.Propositional 
    open import Relation.Nullary.Negation
    open import Data.List.Relation.Unary.Any renaming (here to hereₗ ; there to thereₗ)
    open import Data.Empty


    ∈ₚ-to-∈ : x ∶ A ∈[ p ] Γ → x ∶ A ∈ Γ  
    ∈ₚ-to-∈ here′ = here
    ∈ₚ-to-∈ (there′ ∈Γ x≠y) = there (∈ₚ-to-∈ ∈Γ) x≠y

    ∈-to-∈-dom : x ∶ A ∈ Γ → x ∈ dom Γ  
    ∈-to-∈-dom here = hereₗ refl
    ∈-to-∈-dom (there ∈Γ x) = thereₗ (∈-to-∈-dom ∈Γ)

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

    ++-injective : Γ₁ ,[ p ] x ∶ A ≡ Γ₂ ,[ q ] y ∶ B → Γ₁ ≡ Γ₂  
    ++-injective refl = refl 
    
