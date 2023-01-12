open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import GTTM.Quantity

module GTTM.Normalization (Quant : Set) (IsQuant : IsQuantity Quant) where
                
    open import GTTM.Syntax Quant
    open import GTTM.Substitution Quant IsQuant 
    open import GTTM.Context Quant IsQuant 
    
    open import Data.Nat

    data _▷_ : Term → Term → Set where 
        par-star : ⋆ ▷ ⋆ 
        par-mult : mult ▷ mult 
        par-var : ∀ x → (` x) ▷ (` x)
        par-quant : ∀ ρ → (ρ ₘ) ▷ (ρ ₘ)
        par-bind : ∀ {p p′ A A′ B B′} b → 
            p ▷ p′ →
            A ▷ A′ →
            B ▷ B′ →
            ------------------------------------
            (b ⟦ p ⟧∶ A ⇒ B) ▷ (b ⟦ p′ ⟧∶ A′ ⇒ B′)
        par-mbinop : ∀ {p p′ q q′} b → 
            p ▷ p′ →
            q ▷ q′ →
            -------------------------
            (p ⟪ b ⟫ q) ▷ (p′ ⟪ b ⟫ q′)
        par-app : ∀ {s s′ t t′} →
            s ▷ s′ →
            t ▷ t′ →
            ------------------
            (s ∙ t) ▷ (s′ ∙ t′)
        par-reduce : ∀ {S S′ T T′} p A → 
            S ▷ S′ → 
            T ▷ T′ →
            -----------------------------------------
            ((ƛ ⟦ p ⟧∶ A ⇒ S) ∙ T) ▷ (S′ [ T′ · ids ])

    _▷▷_ : Subst → Subst → Set
    (σ ▷▷ τ) = ∀ x → σ x ▷ τ x 


    par-rename : ∀ {s s′ } ξ → s ▷ s′ → rename ξ s ▷ rename ξ s′
    par-rename ξ par-star = par-star
    par-rename ξ par-mult = par-mult
    par-rename ξ (par-var x) = par-var (ξ x)
    par-rename ξ (par-quant ρ) = par-quant ρ
    par-rename ξ (par-bind b p▷p′ A▷A′ B▷B′) = 
        par-bind b (par-rename ξ p▷p′) (par-rename ξ A▷A′) (par-rename (ext ξ) B▷B′) 
    par-rename ξ (par-mbinop b p▷p′ q▷q′) = par-mbinop b (par-rename ξ p▷p′) (par-rename ξ q▷q′)
    par-rename ξ (par-app s▷s′ t▷t′) = par-app (par-rename ξ s▷s′) (par-rename ξ t▷t′)
    par-rename ξ (par-reduce {S′ = S′} {T′ = T′} p A s▷s′ t▷t′) 
        with ih ← par-reduce (rename ξ p) (rename ξ A) (par-rename (ext ξ) s▷s′) (par-rename ξ t▷t′) 
        rewrite rename-subst-commute ξ S′ T′ 
        = ih 

    par-subst-⇑ : ∀ {σ σ′} → σ ▷▷ σ′ → ⇑ σ ▷▷ ⇑ σ′      
    par-subst-⇑ σ▷▷σ′ zero = par-var zero
    par-subst-⇑ σ▷▷σ′ (suc x) = par-rename suc (σ▷▷σ′ x)

    par-subst : ∀ {s s′ σ σ′} → s ▷ s′ → σ ▷▷ σ′ → (s [ σ ]) ▷ (s′ [ σ′ ])
    par-subst par-star σ▷▷σ′ = par-star
    par-subst par-mult σ▷▷σ′ = par-mult
    par-subst (par-var x) σ▷▷σ′ = σ▷▷σ′ x
    par-subst (par-quant ρ) σ▷▷σ′ = par-quant ρ
    par-subst (par-bind b p▷p′ A▷A′ B▷B′) σ▷▷σ′ = 
        par-bind b (par-subst p▷p′ σ▷▷σ′) (par-subst A▷A′ σ▷▷σ′) (par-subst B▷B′ (par-subst-⇑ σ▷▷σ′))
    par-subst (par-mbinop b p▷p′ q▷q′) σ▷▷σ′ = par-mbinop b (par-subst p▷p′ σ▷▷σ′) (par-subst q▷q′ σ▷▷σ′)
    par-subst (par-app s▷s t▷t′) σ▷▷σ′ = par-app (par-subst s▷s σ▷▷σ′) (par-subst t▷t′ σ▷▷σ′)
    par-subst {σ = σ} {σ′ = σ′} (par-reduce {S′ = S′} {T′ = T′} p A s▷s′ t▷t′) σ▷▷σ′
        with ih ← par-reduce (p [ σ ]) (A [ σ ]) (par-subst s▷s′ (par-subst-⇑ σ▷▷σ′)) (par-subst t▷t′ σ▷▷σ′) 
        rewrite subst-lemma σ′ S′ T′  
        = ih

    par-cons-ids : ∀ {t t′} → t ▷ t′ → (t · ids) ▷▷ (t′ · ids)
    par-cons-ids {t = t} {t′ = t′} t▷t′ zero = t▷t′
    par-cons-ids {t = t} {t′ = t′} t▷t′ (suc x) = par-var x 
    
    _⁺ : Term → Term     
    ⋆ ⁺ = ⋆
    mult ⁺ = mult
    (ρ ₘ) ⁺ = ρ ₘ
    (p ⟪ b ⟫ q) ⁺ = (p ⁺) ⟪ b ⟫ (q ⁺)
    (b ⟦ p ⟧∶ A ⇒ B) ⁺ = b ⟦ p ⁺ ⟧∶ (A ⁺) ⇒ (B ⁺) 
    (` x) ⁺ = ` x
    ((ƛ ⟦ p ⟧∶ A ⇒ s) ∙ t) ⁺ = (s ⁺) [ (t ⁺) · ids ]
    (s ∙ t) ⁺ = (s ⁺) ∙ (t ⁺)

    par-triangle : ∀ {s s′} → s ▷ s′ → s′ ▷ (s ⁺)
    par-triangle par-star = par-star
    par-triangle par-mult = par-mult
    par-triangle (par-var x) = par-var x
    par-triangle (par-quant ρ) = par-quant ρ
    par-triangle (par-bind b p▷p′ A▷A′ B▷B′) = par-bind b (par-triangle p▷p′) (par-triangle A▷A′) (par-triangle B▷B′)
    par-triangle (par-mbinop b p▷p′ q▷q′) = par-mbinop b (par-triangle p▷p′) (par-triangle q▷q′)
    par-triangle (par-app {s = ƛ ⟦ p ⟧∶ A ⇒ s} (par-bind {p′ = p′} {A′ = A′} ƛ p▷p′ A▷A′ s▷s′) t▷t′) = 
        par-reduce p′ A′ (par-triangle s▷s′) (par-triangle t▷t′) 
    par-triangle (par-app {s = ⋆} s▷s′ t▷t′) = par-app (par-triangle s▷s′) (par-triangle t▷t′) 
    par-triangle (par-app {s = mult} s▷s′ t▷t′) = par-app (par-triangle s▷s′) (par-triangle t▷t′) 
    par-triangle (par-app {s = _ ₘ} s▷s′ t▷t′) = par-app (par-triangle s▷s′) (par-triangle t▷t′) 
    par-triangle (par-app {s = ` _} s▷s′ t▷t′) = par-app (par-triangle s▷s′) (par-triangle t▷t′) 
    par-triangle (par-app {s = _ ∙ _} s▷s′ t▷t′) = par-app (par-triangle s▷s′) (par-triangle t▷t′) 
    par-triangle (par-app {s = _ ⟪ _ ⟫ _} s▷s′ t▷t′) = par-app (par-triangle s▷s′) (par-triangle t▷t′) 
    par-triangle (par-app {s = Π ⟦ _ ⟧∶ _ ⇒ _} s▷s′ t▷t′) = par-app (par-triangle s▷s′) (par-triangle t▷t′) 
    par-triangle (par-reduce p A s▷s′ t▷t′) = par-subst (par-triangle s▷s′) (par-cons-ids (par-triangle t▷t′)) 

