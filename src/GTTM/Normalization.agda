open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import GTTM.Quantity

module GTTM.Normalization (Quant : Set) (IsQuant : IsQuantity Quant) where
                


    open import GTTM.Syntax Quant
    open import GTTM.Substitution Quant IsQuant 
    open import GTTM.Context Quant IsQuant 
    
    open import Data.Nat

    private
        variable
            x y n : ℕ
            p p′ q q′ r s s′ t t′ u v a b b′ c : Term n
            ρ ϕ π : Quant
            S S′ T T′ A A′ B : Type n
            Γ Γ′ : Context n 

        module Q = IsQuantity IsQuant

    infix 2 _⟶_
    data _⟶_ : Term n → Term n → Set where 
        -- t ≡ ↓₁ 0 (a [ ↑ 1 0 b / 0 ])
        β-reduce : t ≡ ↓₁ 0 (s≤s z≤n) (no-var-subst a (no-var-incr {c = 0} {r = 1} b z≤n (s≤s z≤n))) → (ƛ[ p ]∶ A ⇒ a) ∙ b ⟶ t 
    --     -- +-known : ((ρ ₘ) +ₘ (π ₘ)) ⟶ (ρ Q.+ π) ₘ
    --     -- ·-known : ((ρ ₘ) ·ₘ (π ₘ)) ⟶ (ρ Q.· π) ₘ
    --     -- +-0ₗ : (Q.zero ₘ) +ₘ p ⟶ p  
    --     -- +-0ᵣ : p +ₘ (Q.zero ₘ) ⟶ p  
    --     -- ·-0ₗ : (Q.zero ₘ) ·ₘ p ⟶ (Q.zero ₘ)  
    --     -- ·-0ᵣ : p ·ₘ (Q.zero ₘ) ⟶ (Q.zero ₘ)

    
    -- infix 3 _↠_
    -- data _↠_ : Term → Term → Set where 
    --     refl-↠ : s ↠ s 
    --     trans-↠ : a ↠ b → (b⟶c : b ⟶ c) → a ↠ c   

    -- trans-↠′ : a ↠ b → b ↠ c → a ↠ c
    -- trans-↠′ a↠b refl-↠ = a↠b 
    -- trans-↠′ a↠b (trans-↠ b↠c b⟶c) = trans-↠ (trans-↠′ a↠b b↠c) b⟶c

    -- confluence-reduction : a ⟶ s → a ⟶ t → s ≡ t 
    -- confluence-reduction (β-reduce pf₁) (β-reduce pf₂) = trans pf₁ (sym pf₂)
    -- -- confluence-reduction +-known +-known = refl
    -- -- confluence-reduction (+-known {π = π}) +-0ₗ rewrite Q.+-identity π = refl
    -- -- confluence-reduction (+-known {ρ = ρ}) +-0ᵣ rewrite Q.+-comm ρ Q.zero rewrite Q.+-identity ρ = refl
    -- -- confluence-reduction ·-known ·-known = refl
    -- -- confluence-reduction (·-known {π = π}) ·-0ₗ rewrite Q.0-cancelₗ π = refl
    -- -- confluence-reduction (·-known {ρ = ρ}) ·-0ᵣ rewrite Q.0-cancelᵣ ρ = refl
    -- -- confluence-reduction +-0ₗ (+-known {π = π}) rewrite Q.+-identity π = refl
    -- -- confluence-reduction +-0ₗ +-0ₗ = refl
    -- -- confluence-reduction +-0ₗ +-0ᵣ = refl
    -- -- confluence-reduction +-0ᵣ (+-known {ρ = ρ}) rewrite Q.+-comm ρ Q.zero rewrite Q.+-identity ρ = refl
    -- -- confluence-reduction +-0ᵣ +-0ₗ = refl
    -- -- confluence-reduction +-0ᵣ +-0ᵣ = refl
    -- -- confluence-reduction ·-0ₗ (·-known {π = π}) rewrite Q.0-cancelₗ π = refl
    -- -- confluence-reduction ·-0ₗ ·-0ₗ = refl
    -- -- confluence-reduction ·-0ₗ ·-0ᵣ = refl
    -- -- confluence-reduction ·-0ᵣ (·-known {ρ = ρ}) rewrite Q.0-cancelᵣ ρ = refl
    -- -- confluence-reduction ·-0ᵣ ·-0ₗ = refl
    -- -- confluence-reduction ·-0ᵣ ·-0ᵣ = refl


        


    -- open import Data.Product
    -- open import Relation.Nullary

    -- data _▷_ : Term → Term → Set where 
    --     par-star : ⋆ ▷ ⋆ 
    --     par-mult : mult ▷ mult 
    --     par-var : (` x) ▷ (` x)
    --     par-quant : (ρ ₘ) ▷ (ρ ₘ)
    --     par-pi :
    --         p ▷ p′ → 
    --         S ▷ S′ → 
    --         T ▷ T′ → 
    --         -------------------------------------------
    --         (⦅[ p ] x ∶ S ⦆⇒ T) ▷ (⦅[ p′ ] x ∶ S′ ⦆⇒ T′)
    --     par-lam :
    --         p ▷ p′ → 
    --         S ▷ S′ → 
    --         b ▷ b′ → 
    --         ------------------------------------------
    --         (ƛ[ p ] x ∶ S ⇒ b) ▷ (ƛ[ p′ ] x ∶ S′ ⇒ b′)
    --     par-app :
    --         s ▷ s′ →
    --         t ▷ t′ →
    --         -------------------
    --         (s ∙ t) ▷ (s′ ∙ t′)
    --     par-plus :
    --         p ▷ p′ →
    --         q ▷ q′ →
    --         ---------------------
    --         (p +ₘ q) ▷ (p′ +ₘ q′)
    --     par-times :
    --         p ▷ p′ →
    --         q ▷ q′ →
    --         ---------------------
    --         (p ·ₘ q) ▷ (p′ ·ₘ q′)
    --     par-reduce :
    --         s ▷ s′ → 
    --         t ▷ t′ →  
    --         -------------------------------------
    --         ((ƛ[ p ] x ∶ S ⇒ t) ∙ s) ▷ (t′ [ s′ / x ])

    -- par-refl : ∀ a → a ▷ a 
    -- par-refl ⋆ = par-star
    -- par-refl mult = par-mult
    -- par-refl (p +ₘ q) = par-plus (par-refl p) (par-refl q)
    -- par-refl (p ·ₘ q) = par-times (par-refl p) (par-refl q)
    -- par-refl (ρ ₘ) = par-quant 
    -- par-refl (⦅[ p ] x ∶ A ⦆⇒ B) = par-pi (par-refl p) (par-refl A) (par-refl B)
    -- par-refl (ƛ[ p ] x ∶ A ⇒ B) = par-lam (par-refl p) (par-refl A) (par-refl B)
    -- par-refl (` x) = par-var
    -- par-refl (s ∙ t) = par-app (par-refl s) (par-refl t) 

    -- par-refl′ : a ▷ a
    -- par-refl′ {a = a} = par-refl a
     



    -- subst-par : s ▷ t → a ▷ b → (s [ a / x ]) ▷ (t [ b / x ])
    -- subst-par par-star a▷b = par-star
    -- subst-par par-mult a▷b = par-mult
    -- subst-par {x = x} (par-var {x = y}) a▷b with x ≟ y
    -- ... | yes refl = a▷b
    -- ... | no contra = par-var
    -- subst-par par-quant a▷b = par-quant
    -- subst-par (par-pi s▷t s▷t₁ s▷t₂) a▷b = {!   !}
    -- subst-par (par-lam s▷t s▷t₁ s▷t₂) a▷b = {!   !}
    -- subst-par (par-app s▷t s▷t₁) a▷b = {!   !}
    -- subst-par (par-plus s▷t s▷t₁) a▷b = {!   !}
    -- subst-par (par-times s▷t s▷t₁) a▷b = {!   !}
    -- subst-par {a = e} {b = e′} {x = y} (par-reduce  {s = s} {s′ = s′} {t = t} {t′ = t′} {p = p} {x = x} {S = S} s▷s′ t▷t′) e▷e′ 
    --     with ihₛ ← subst-par {x = y} s▷s′ e▷e′
    --     with ihₜ ← subst-par {x = y} t▷t′ e▷e′
    --     with ihₚ ← subst-par {x = x} t▷t′ s▷s′ 
    --     with y ≟ x 
    -- ... | yes refl rewrite subst-assoc {e′} {s′} {y} t′ = par-reduce ihₛ t▷t′
    -- ... | no x≠y =
    --     let hyp = par-reduce {p = p [ e / y ]} {x = x} {S = S [ e / y ]} s▷s′ ihₜ in {!   !}
    --     -- somehow need x ∉ fvs e 
    --     -- let subst≡ = trans (subst-commute e′ (s′ [ e′ / y ]) t′ x≠y) (sym (subst-assoc′ s′ e′ x y t′)) in
    --     -- subst (((ƛ[ p [ e / y ] ] x ∶ S [ e / y ] ⇒ (t [ e / y ])) ∙ (s [ e / y ])) ▷_) subst≡ hyp 