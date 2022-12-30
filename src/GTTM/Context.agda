open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import GTTM.Quantity


module GTTM.Context (Quant : Set) (IsQuant : IsQuantity Quant) where 
    open import GTTM.Syntax Quant
    open import Data.Nat
    open import Data.Product
    open import GTTM.Substitution Quant IsQuant

    private 
        variable    
            n : ℕ

    data PreContext : ℕ → Set where
        ∅ₚ : PreContext n
        _,,_ : PreContext n → Type n → PreContext (suc n)

    data Context : ℕ → Set where 
        ∅ : Context n
        _,[_]_ : Context n → Term n → Type n → Context (suc n)

    private
        variable
            p q r s t : Term n
            S T A B : Type n
            Γ Γ₁ Γ₂ Γ₃ Δ : Context n
            Γₚ Δₚ ⌊Γ₁⌋ ⌊Γ₂⌋ : PreContext n
            ρ ϕ : Quant

    ⌊_⌋ : Context n → PreContext n
    ⌊ ∅ ⌋ = ∅ₚ
    ⌊ Δ ,[ q ] t ⌋ = ⌊ Δ ⌋ ,, t 

    data HasPreContext : (n : ℕ) → Context n → PreContext n → Set where 
        has-∅ₚ : HasPreContext n ∅ ∅ₚ
        has-, :  HasPreContext n Γ Γₚ → ∀ p A → HasPreContext (suc n) (Γ ,[ p ] A) (Γₚ ,, A)

    hasPreContext : (Γ : Context n) → HasPreContext n Γ ⌊ Γ ⌋
    hasPreContext ∅ = has-∅ₚ
    hasPreContext (Γ ,[ p ] A) = has-, (hasPreContext Γ) p A

    hpc→≡ : HasPreContext n Γ Γₚ → ⌊ Γ ⌋ ≡ Γₚ 
    hpc→≡  has-∅ₚ = refl
    hpc→≡ (has-, hpc _ A) = cong (_,, A) (hpc→≡ hpc) 

    ≡→hpc : ⌊ Γ ⌋ ≡ Γₚ → HasPreContext n Γ Γₚ    
    ≡→hpc {Γ = Γ} refl = hasPreContext Γ

    -- preContextInjective : (⌊Γ₁⌋ , x ∶ A) ≡ (⌊Γ₂⌋ , y ∶ B) → ⌊Γ₁⌋ ≡ ⌊Γ₂⌋
    -- preContextInjective refl = refl 

    -- preContextLemma : (⌊Γ₁⌋ , x ∶ A) ≡ (⌊Γ₂⌋ , y ∶ B) → x ≡ y × A ≡ B 
    -- preContextLemma refl = refl , refl

    -- samePreContext : (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) → HasPreContext Γ₁ ⌊ Γ₂ ⌋
    -- samePreContext {Γ₁ = Γ₁} {Γ₂ = Γ₂} Γ₁₂-≡ = subst (HasPreContext Γ₁) Γ₁₂-≡ (hasPreContext Γ₁) 

    
    private
        module Q = IsQuantity IsQuant

    infix 50 𝟘_
    𝟘_ : Context n → Context n
    𝟘 ∅ = ∅
    𝟘 (Γ ,[ p ] T) = 𝟘 Γ ,[ Q.zero ₘ ] T

    𝟘-idempotent : ∀ (Γ : Context n) → 𝟘 (𝟘 Γ) ≡ 𝟘 Γ
    𝟘-idempotent ∅ = refl
    𝟘-idempotent (Γ ,[ p ] T) = cong (_,[ Q.zero ₘ ] T) (𝟘-idempotent Γ)

    -- _++_ : Context n → Context n → Context n
    -- Γ₁ ++ ∅ = Γ₁
    -- Γ₁ ++ (Γ₂ ,[ p ] x ∶ A) = (Γ₁ ++ Γ₂) ,[ p ] x ∶ A

    -- infixl 5 _++_

    -- _+_[_] : (Γ₁ : Context) → (Γ₂ : Context) → (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) → Context 
    -- Γ₁ + Γ₂ [ Γ₁₂-≡ ] = go Γ₁ Γ₂ (samePreContext Γ₁₂-≡) (hasPreContext Γ₂) 
    --     where
    --     go : (Γ₁ : Context) → (Γ₂ : Context) → HasPreContext Γ₁ ⌊ Γ₂ ⌋ →  HasPreContext Γ₂ ⌊ Γ₂ ⌋ → Context  
    --     go ∅ ∅ has-∅ₚ has-∅ₚ = ∅
    --     go ∅ (Γ₂ ,[ x ] x₁ ∶ x₂) () hpc₂
    --     go (Γ₁ ,[ x ] x₁ ∶ x₂) ∅ () hpc₂
    --     go (Γ₁ ,[ p ] x ∶ A) (Γ₂ ,[ q ] x ∶ A) (has-, hpc₁) (has-, hpc₂) = go Γ₁ Γ₂ hpc₁ hpc₂  

    -- infix 2 _≤_ 
    -- data _≤_ : Context → Context → Set where
    --     ≤-∅ : ∅ ≤ ∅ 
    --     ≤-, : Γ₁ ≤ Γ₂ → ρ Qu.≤ ϕ → Γ₁ ,[ ρ ₘ ] x ∶ A ≤ Γ₂ ,[ ϕ ₘ ] x ∶ A

    -- open import Data.List hiding (_++_)
    -- dom : Context → List Var  
    -- dom ∅ = []
    -- dom (Γ ,[ _ ] x ∶ _) = x ∷ dom Γ

    -- data _∶_∈_ : Var → Term → Context → Set where
    --     here : x ∶ A ∈ (Γ ,[ p ] x ∶ A)
    --     there : x ∶ A ∈ Γ → x ≢ y → x ∶ A ∈ (Γ ,[ p ] y ∶ B)

    -- data _∶_∈[_]_ : Var → Term → Term → Context → Set where
    --     here′ : x ∶ A ∈[ p ] (Γ ,[ p ] x ∶ A)
    --     there′ : x ∶ A ∈[ p ] Γ → x ≢ y → x ∶ A ∈[ p ] (Γ ,[ q ] y ∶ B)

    -- ∈-respects-≤ : (x ∶ A ∈ Γ₁) → Γ₁ ≤ Γ₂ → (x ∶ A ∈ Γ₂)
    -- ∈-respects-≤ here (≤-, ≤-Γ ρ≤ϕ) = here
    -- ∈-respects-≤ (there ∈Γ₁ x≠y) (≤-, ≤-Γ x) = there (∈-respects-≤ ∈Γ₁ ≤-Γ) x≠y

    -- ∈-respects-≥ : (x ∶ A ∈ Γ₁) → Γ₂ ≤ Γ₁ → (x ∶ A ∈ Γ₂)
    -- ∈-respects-≥ here (≤-, ≤-Γ ρ≤ϕ) = here
    -- ∈-respects-≥ (there ∈Γ₁ x≠y) (≤-, ≤-Γ x) = there (∈-respects-≥ ∈Γ₁ ≤-Γ) x≠y 

    -- -- ∈-respects-≥ : (x ∶ A ∈[ p ] Γ₁) → Γ₂ ≤ Γ₁ → ∃[ ϕ ] (x ∶ A ∈[ ϕ ₘ ] Γ₂) × ϕ ₘ ≤ p  


    -- open import Data.List.Membership.Propositional 
    -- open import Relation.Nullary.Negation
    -- open import Data.List.Relation.Unary.Any renaming (here to hereₗ ; there to thereₗ)
    -- open import Data.Empty


    -- ∈ₚ-to-∈ : x ∶ A ∈[ p ] Γ → x ∶ A ∈ Γ  
    -- ∈ₚ-to-∈ here′ = here
    -- ∈ₚ-to-∈ (there′ ∈Γ x≠y) = there (∈ₚ-to-∈ ∈Γ) x≠y

    -- ∈-to-∈-dom : x ∶ A ∈ Γ → x ∈ dom Γ  
    -- ∈-to-∈-dom here = hereₗ refl
    -- ∈-to-∈-dom (there ∈Γ x) = thereₗ (∈-to-∈-dom ∈Γ)

    -- Γ-∈-≡ : x ∶ A ∈ Γ₁ → x ∶ B ∈ Γ₂ → Γ₁ ≡ Γ₂ → A ≡ B 
    -- Γ-∈-≡ here here refl = refl
    -- Γ-∈-≡ here (there ∈Γ₂ x≠x) refl = ⊥-elim (x≠x refl)
    -- Γ-∈-≡ (there ∈Γ₁ x≠x) here refl = ⊥-elim (x≠x refl)
    -- Γ-∈-≡ (there ∈Γ₁ x≠y) (there ∈Γ₂ y≠z) refl = Γ-∈-≡ ∈Γ₁ ∈Γ₂ refl 

    -- Γ-++ : x ∉ dom Γ₂ → x ∶ A ∈ ((Γ₁ ,[ p ] x ∶ A) ++ Γ₂)
    -- Γ-++ {Γ₂ = ∅} x∉Γ₂ = here
    -- Γ-++ {Γ₂ = Γ₂ ,[ q ] y ∶ B} x∉Γ₂ = there (Γ-++ (∈-cons x∉Γ₂)) (∈-≢ x∉Γ₂)
    --     where
    --     ∈-cons : ∀ {x y} {xs : List Var} → x ∉ y ∷ xs → x ∉ xs 
    --     ∈-cons ∉yxs (hereₗ px) = ∉yxs (thereₗ (hereₗ px))
    --     ∈-cons ∉yxs (thereₗ ∈xs) = ∉yxs (thereₗ (thereₗ ∈xs)) 

    --     ∈-≢ : ∀ {x y} {xs : List Var} → x ∉ y ∷ xs → x ≢ y 
    --     ∈-≢ ∉yxs x=y = ∉yxs (hereₗ x=y)

    -- ++-injective : Γ₁ ,[ p ] x ∶ A ≡ Γ₂ ,[ q ] y ∶ B → Γ₁ ≡ Γ₂  
    -- ++-injective refl = refl 
    
