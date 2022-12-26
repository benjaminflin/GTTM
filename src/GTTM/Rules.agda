open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import GTTM.Quantity

module GTTM.Rules  (Quant : Set) (IsQuant : IsQuantity Quant) where
    
    -- open import GTTM.Syntax Var Quant
    -- open import GTTM.Context Var Quant IsQuant
    -- open import GTTM.Substitution Var _≟_ Quant IsQuant 
    -- open import GTTM.Normalization Var _≟_ Quant IsQuant 
    -- open import Data.List.Membership.Propositional 

    -- private
    --     variable
    --         x : Var
    --         ρ : Quant
    --         s t a b : Term
    --         p q r : Term
    --         A B C S T R : Type
    --         Γ Γ₁ Γ₂ Γ₃ Γ₄ : Context 
    --         Γₚ Δₚ : PreContext 

    -- open IsQuantity IsQuant using (one; zero)

    -- data _⊢_∶_ : Context → Term → Type → Set where
    --     t-var : 
    --         (𝟘Γ : Γ ≡ 𝟘 Γ) →
    --         (⊢T : Γ ⊢ T ∶ ⋆) →
    --         ------------------------------
    --         (Γ ,[ one ₘ ] x ∶ T) ⊢ ` x ∶ T

    --     t-mult-type :
    --         ------------
    --         ∅ ⊢ mult ∶ ⋆

    --     t-type-type : 
    --         ---------
    --         ∅ ⊢ ⋆ ∶ ⋆  

    --     t-mult-intro :
    --         --------------
    --         ∅ ⊢ ρ ₘ ∶ mult
        
    --     t-mult-+ :
    --         (⊢p : Γ₁ ⊢ p ∶ mult) →
    --         (⊢q : Γ₂ ⊢ q ∶ mult) →
    --         (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
    --         (Γ-split : (Γ₁ + Γ₂ [ Γ₁₂-≡ ]) ≡ Γ) →
    --         -----------------
    --         Γ ⊢ p +ₘ q ∶ mult

    --     t-mult-· :
    --         (⊢p : Γ₁ ⊢ p ∶ mult) →
    --         (⊢q : Γ₂ ⊢ q ∶ mult) →
    --         (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
    --         (Γ-split : (Γ₁ + Γ₂ [ Γ₁₂-≡ ]) ≡ Γ) →
    --         -----------------
    --         Γ ⊢ p ·ₘ q ∶ mult 

    --     t-lam : 
    --         (⊢a : (Γ₁ ,[ p ] x ∶ A) ⊢ a ∶ B) →
    --         (⊢p : Γ₂ ⊢ p ∶ mult) → 
    --         (⊢A : Γ₃ ⊢ A ∶ ⋆) →
    --         (⊢B : (Γ₄ ,[ r ] x ∶ A) ⊢ B ∶ ⋆) →
    --         (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
    --         (Γ₁₃-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₃ ⌋) →
    --         (Γ₁₃-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₄ ⌋) →
    --         --------------------------------------------
    --         Γ₁ ⊢ (ƛ[ p ] x ∶ A ⇒ a) ∶ (⦅[ p ] x ∶ A ⦆⇒ B)

    --     t-pi :
    --         (⊢p : Γ₁ ⊢ p ∶ mult) →
    --         (⊢A : Γ₂ ⊢ A ∶ ⋆) →
    --         (⊢B : (Γ₃ ,[ r ] x ∶ A) ⊢ B ∶ ⋆) →
    --         (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
    --         (Γ₁₃-≡ : ⌊ Γ₁ + Γ₂ [ Γ₁₂-≡ ] ⌋ ≡ ⌊ Γ₃ ⌋) →
    --         (Γ-split : ((Γ₁ + Γ₂ [ Γ₁₂-≡ ]) + Γ₃ [ Γ₁₃-≡ ]) ≡ Γ) → 
    --         ---------------------------- 
    --         Γ ⊢ (⦅[ p ] x ∶ A ⦆⇒ B) ∶ ⋆ 
        
    --     t-app :
    --         (⊢s : Γ₁ ⊢ s ∶ (⦅[ p ] x ∶ A ⦆⇒ B)) →
    --         (⊢t : Γ₂ ⊢ t ∶ A) →
    --         (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ p · Γ₂ ⌋) →
    --         (Γ-split : (Γ₁ + (p · Γ₂) [ Γ₁₂-≡ ]) ≡ Γ) →
    --         (R-conv : R ≡ (B [ t / x ])) →
    --         ------------------------------
    --         Γ ⊢ (s ∙ t) ∶ R 
        
    --     t-sub :
    --         (⊢a : Γ₁ ⊢ a ∶ A) → 
    --         (Γ-≤ : Γ₁ ≤ Γ₂) → 
    --         (Γ₁₂-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋) →
    --         ---------------------------
    --         Γ₂ ⊢ a ∶ A 
        
    --     t-weak :
    --         (⊢b : Γ₁ ⊢ b ∶ B) →
    --         (⊢A : Γ₂ ⊢ A ∶ ⋆) →
    --         (∉Γ₁ : x ∉ dom Γ₁) →
    --         ------------------------------
    --         (Γ₁ ,[ zero ₘ ] x ∶ A) ⊢ b ∶ B

    --     t-conv :
    --         (▸a : a ↠ t) →
    --         (▸b : b ↠ t) →
    --         (▸A : A ↠ T) →
    --         (▸B : B ↠ T) →
    --         (⊢a : Γ ⊢ a ∶ A) →
    --         (⊢A : Γ ⊢ A ∶ ⋆) →
    --         -------------------
    --         Γ ⊢ b ∶ B

    -- -- convenience type
    -- data _⊢_≣_ : Context → Term → Term → Set where
    --     conv :
    --         (▸A : A ↠ T) →
    --         (▸B : B ↠ T) →
    --         (⊢A : Γ ⊢ A ∶ ⋆) →
    --         (⊢B : Γ ⊢ B ∶ ⋆) →
    --         -------------------
    --         Γ ⊢ A ≣ B 


    -- conv-refl : (⊢A : Γ ⊢ A ∶ ⋆) → Γ ⊢ A ≣ A  
    -- conv-refl p = conv refl-↠ refl-↠ p p
    
    -- conv-sym : Γ ⊢ A ≣ B → Γ ⊢ B ≣ A    
    -- conv-sym (conv ▸A ▸B ⊢A ⊢B) = conv ▸B ▸A ⊢B ⊢A

    -- conv-trans : Γ ⊢ A ≣ B → Γ ⊢ B ≣ C → Γ ⊢ A ≣ C 
    -- conv-trans (conv ▸A ▸B ⊢A ⊢B) (conv ▸C ▸D ⊢C ⊢D) = conv ▸A {!   !} {!   !} {!   !}