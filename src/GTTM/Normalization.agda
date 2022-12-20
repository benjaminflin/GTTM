open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import GTTM.Quantity

module GTTM.Normalization (Var : Set) (_≟_ : DecidableEquality Var) (Quant : Set) (IsQuant : IsQuantity Quant) where
                
    open import GTTM.Syntax Var Quant
    open import GTTM.Substitution Var _≟_ Quant IsQuant 
    open import GTTM.Context Var Quant IsQuant 
    
    private
        variable
            x y : Var
            p p′ q q′ r s t u v a b c : Term
            ρ ϕ π : Quant
            S T A A′ B : Type
            Γ Γ′ : Context 

        module Q = IsQuantity IsQuant

    infix 2 _⟶_
    data _⟶_ : Term → Term → Set where 
        β-reduce : t ≡ a [ b / x ] → (ƛ[ p ] x ∶ A ⇒ a) ∙ b ⟶ t 
        +-known : ((ρ ₘ) +ₘ (π ₘ)) ⟶ (ρ Q.+ π) ₘ
        ·-known : ((ρ ₘ) ·ₘ (π ₘ)) ⟶ (ρ Q.· π) ₘ
        +-0ₗ : (Q.zero ₘ) +ₘ p ⟶ p  
        +-0ᵣ : p +ₘ (Q.zero ₘ) ⟶ p  
        ·-0ₗ : (Q.zero ₘ) ·ₘ p ⟶ (Q.zero ₘ)  
        ·-0ᵣ : p ·ₘ (Q.zero ₘ) ⟶ (Q.zero ₘ)

    infix 2 _▸_
    data _▸_ : Term → Term → Set where 
        refl-▸ : s ▸ s 
        trans-▸ : a ▸ b → (b⟶c : b ⟶ c) → a ▸ c   

    trans-▸′ : a ▸ b → b ▸ c → a ▸ c
    trans-▸′ a▸b refl-▸ = a▸b 
    trans-▸′ a▸b (trans-▸ b▸c b⟶c) = trans-▸ (trans-▸′ a▸b b▸c) b⟶c


