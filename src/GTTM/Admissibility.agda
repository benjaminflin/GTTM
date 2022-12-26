open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import GTTM.Quantity

module GTTM.Admissibility (Quant : Set) (IsQuant : IsQuantity Quant) where

    -- open import GTTM.Syntax Var Quant
    -- open import GTTM.Context Var Quant IsQuant
    -- open import GTTM.Substitution Var _≟_ Quant IsQuant  
    -- open import GTTM.Rules Var _≟_ Quant IsQuant 
    -- open import GTTM.Normalization Var _≟_ Quant IsQuant 

    -- private
    --     variable
    --         x y : Var
    --         p p′ q q′ r s t u v a b c : Term
    --         S T A B : Type
    --         Γ Γ₁ Γ₂ Δ : Context
    
    -- open import Relation.Nullary
    -- open import Data.Product
    -- open import Data.Empty
    -- open import Data.List.Membership.Propositional 
    -- open import Data.List.Relation.Unary.Any renaming (here to hereₗ ; there to thereₗ)
    -- open import Relation.Nullary.Negation
    -- open import Function.Base

    -- private module Q = IsQuantity IsQuant

    -- reduction-var-lemma : ` x ▸ a → a ≡ ` x 
    -- reduction-var-lemma refl-▸ = refl
    -- reduction-var-lemma (trans-▸ ▸a b⟶c) rewrite reduction-var-lemma ▸a with () ← b⟶c

    -- ⊢x⇒x∈Γ : Γ ⊢ ` x ∶ A → ∃[ B ] ∃[ Γ′ ] (x ∶ B ∈ Γ × Γ′ ⊢ A ≣ B)  
    -- ⊢x⇒x∈Γ (t-var 𝟘Γ ⊢x) = -, -, here , conv refl-▸ refl-▸ ⊢x 
    -- ⊢x⇒x∈Γ (t-sub ⊢x Γ-≤ Γ₁₂-≡)  
    --     with B , Γ′ , ∈Γ , A=B ← ⊢x⇒x∈Γ ⊢x = -, -, ∈-respects-≤ ∈Γ Γ-≤ , A=B 
    -- ⊢x⇒x∈Γ (t-weak ⊢x ⊢A ∉Γ₁) 
    --     with B , Γ′ , ∈Γ , A=B ← ⊢x⇒x∈Γ ⊢x = 
    --     -, -, there ∈Γ (contraposition (lem (∈-to-∈-dom ∈Γ)) ∉Γ₁) , A=B -- , there ih (contraposition (lem (∈-to-∈-dom ih)) ∉Γ₁) , ?
    --     where
    --         lem : ∀ {x y} → x ∈ dom Γ → x ≡ y → y ∈ dom Γ
    --         lem ⊢x refl = ⊢x
    -- ⊢x⇒x∈Γ {A = B} (t-conv refl-▸ ▸b ▸A ▸B ⊢a ⊢A) rewrite reduction-var-lemma ▸b 
    --     with C , Γ′ , ∈Γ , conv _ ▸C _ ← ⊢x⇒x∈Γ ⊢a = -, -, ∈Γ , conv {!   !} {!   !} {!   !} 
    -- ⊢x⇒x∈Γ {A = B} (t-conv (trans-▸ ▸a b⟶c) ▸b ▸A ▸B ⊢a ⊢A) = {! b⟶c  !}

    -- -- subst-admissible-var-lemma₁ : x ∶ A ∈ Γ → Γ ⊢ ` x ∶ B → A ≡ B   
    -- -- subst-admissible-var-lemma₁ here (t-var 𝟘Γ ⊢T) = refl
    -- -- subst-admissible-var-lemma₁ (there ∈Γ x) (t-var 𝟘Γ ⊢T) = ⊥-elim (x refl)
    -- -- subst-admissible-var-lemma₁ ∈Γ (t-sub ⊢x Γ-≤ Γ₁₂-≡) = subst-admissible-var-lemma₁ (∈-respects-≥ ∈Γ Γ-≤) ⊢x
    -- -- subst-admissible-var-lemma₁ here (t-weak ⊢x ⊢A ∉Γ) = ⊥-elim (∉Γ ((∈-to-∈-dom ∘ ⊢x⇒x∈Γ) ⊢x)) 
    -- -- subst-admissible-var-lemma₁ (there ∈Γ x≠y) (t-weak ⊢x ⊢A ∉Γ) = subst-admissible-var-lemma₁ ∈Γ ⊢x 
    -- -- subst-admissible-var-lemma₁ here (t-conv ▸a ▸b ▸A ▸B ⊢a ⊢A) = {!   !} 
    -- -- subst-admissible-var-lemma₁ (there ∈Γ x≠y) (t-conv ▸a ▸b ▸A ▸B ⊢a ⊢A) = {!   !} 


    -- -- ⊢x⇒x∈Γ (Rules.t-var 𝟘Γ ⊢T) = here 
    -- -- ⊢x⇒x∈Γ (Rules.t-sub ⊢x Γ-≤ Γ₁₂-≡) = ∈-respects-≤ (⊢x⇒x∈Γ ⊢x) Γ-≤ 
    -- -- ⊢x⇒x∈Γ (Rules.t-weak ⊢x ⊢A ∉Γ₁) = 
    -- --     let ih = (⊢x⇒x∈Γ ⊢x) in there ih (contraposition (lem (∈-to-∈-dom ih)) ∉Γ₁) 
    -- --     where
    -- --         lem : ∀ {x y} → x ∈ dom Γ → x ≡ y → y ∈ dom Γ
    -- --         lem ⊢x refl = ⊢x
        
    -- -- subst-admissible-var-sublemma : Δ ,[ p ] x ∶ A ≡ Γ₁ ++ (Γ₂ ,[ q ] y ∶ B) → p ≡ q   
    -- -- subst-admissible-var-sublemma refl = refl

    -- -- subst-admissible-var-lemma₁ : x ∶ A ∈ Γ → Γ ⊢ ` x ∶ B → A ≡ B   
    -- -- subst-admissible-var-lemma₁ Context.here (Rules.t-var 𝟘Γ ⊢T) = refl
    -- -- subst-admissible-var-lemma₁ (Context.there ∈Γ x) (Rules.t-var 𝟘Γ ⊢T) = ⊥-elim (x refl)
    -- -- subst-admissible-var-lemma₁ ∈Γ (Rules.t-sub ⊢x Γ-≤ Γ₁₂-≡) = subst-admissible-var-lemma₁ (∈-respects-≥ ∈Γ Γ-≤) ⊢x
    -- -- subst-admissible-var-lemma₁ Context.here (Rules.t-weak ⊢x ⊢A ∉Γ) = ⊥-elim (∉Γ ((∈-to-∈-dom ∘ ⊢x⇒x∈Γ) ⊢x)) 
    -- -- subst-admissible-var-lemma₁ (Context.there ∈Γ x≠y) (Rules.t-weak ⊢x ⊢A ∉Γ) = subst-admissible-var-lemma₁ ∈Γ ⊢x 


    -- -- subst-admissible-var-lemma₂ : x ∶ A ∈[ p ] Γ → Γ ⊢ ` x ∶ B → ∃[ ϕ ] (p ≡ ϕ ₘ) × (Q.one Q.≤ ϕ)
    -- -- subst-admissible-var-lemma₂ Context.here′ (Rules.t-var 𝟘Γ ⊢x) = Q.one , refl , (Q.≤-refl Q.one)
    -- -- subst-admissible-var-lemma₂ (Context.there′ ∈Γ x) (Rules.t-var 𝟘Γ ⊢x) = ⊥-elim (x refl)
    -- -- subst-admissible-var-lemma₂ ∈Γ (Rules.t-sub ⊢x Γ-≤ Γ₁₂-≡) =
    -- --     let ih = subst-admissible-var-lemma₂ {! ∈-respects-≥ (∈ₚ-to-∈ ?) Γ-≤  !} ⊢x in {!   !}
    -- -- subst-admissible-var-lemma₂ ∈Γ (Rules.t-weak ⊢x ⊢x₁ ∉Γ₁) = subst-admissible-var-lemma₂ {!   !} ⊢x

    -- -- subst-admissible : (Γ-≡ : ⌊ Γ₁ ⌋ ≡ ⌊ p · Γ ⌋) → 
    -- --             (Δ ≡ (Γ₁ ,[ p ] x ∶ A ++ Γ₂)) →
    -- --             Γ ⊢ a ∶ A → 
    -- --             Δ ⊢ b ∶ B → 
    -- --             (Γ₁ + (p · Γ) [ Γ-≡ ] ++ Γ₂) ⊢ (b [ a / x ]) ∶ (B [ a / x ])
    -- -- subst-admissible {x = x} {b = b} Γ-≡ Δ-≡ ⊢a (Rules.t-var {x = y} 𝟘Γ ⊢T) with (x ≟ y) 
    -- -- ... | yes refl = {!   !} -- need to show: A ≡ B ≡ B [ a / x ], Γ₂ = 𝟘Γ₂, p = 1, Γ₁ = 𝟘Γ₁ then can construct result by weakening 
    -- -- ... | no contra = {!   !} -- need to show: p = 0 (since x is not used), and then show typeability after carving out x from Δ
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a Rules.t-mult-type = {!   !}
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a Rules.t-type-type = {!   !}
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a Rules.t-mult-quant = {!   !}
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-mult-+ ⊢b ⊢b₁ Γ₁₂-≡ Γ-split) = {!   !}
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-mult-· ⊢b ⊢b₁ Γ₁₂-≡ Γ-split) = {!   !}
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-lam ⊢b ⊢b₁ ⊢b₂ ⊢b₃ Γ₁₂-≡ Γ₁₃-≡ Γ₁₄-≡) = {!   !}
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-pi ⊢b ⊢b₁ ⊢b₂ Γ₁₂-≡ Γ₁₃-≡ Γ-split) = {!   !}
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-app ⊢b ⊢b₁ Γ₁₂-≡ Γ-split R-conv) = {!   !}
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-sub ⊢b Γ-≤ Γ₁₂-≡) = {!   !}
    -- -- subst-admissible Γ-≡ Δ-≡ ⊢a (Rules.t-weak ⊢x ⊢A ∉Γ) = {!   !}
