open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import GTTM.Quantity

module GTTM.Normalization (Quant : Set) (IsQuant : IsQuantity Quant) where
                


    open import GTTM.Syntax Quant
    open import GTTM.Substitution Quant IsQuant 
    open import GTTM.Context Quant IsQuant 
    
    open import Data.Nat

    -- private
    --     variable
    --         x y n n′ : ℕ
    --         p p′ q q′ r s s′ t t′ u v a a′ b b′ c : Term n
    --         ρ ϕ π : Quant
    --         S S′ T T′ A A′ B : Type n
    --         Γ Γ′ : Context n 

    --     module Q = IsQuantity IsQuant

    -- beta-reduce : Term (suc n) → Term n → Term n 
    -- beta-reduce a b = ↓₁ 0 z≤n (no-var-subst a (no-var-incr {c = 0} {r = 1} b z≤n (s≤s z≤n)))

    -- infix 2 _⟶_
    -- data _⟶_ : Term n → Term n → Set where 
    --     -- t ≡ ↓₁ 0 (a [ ↑ 1 0 b / 0 ])
    --     β-reduce : t ≡ beta-reduce a b → (ƛ[ p ] refl ∶ A ⇒ a) ∙ b ⟶ t 
    --     -- +-known : ((ρ ₘ) +ₘ (π ₘ)) ⟶ (ρ Q.+ π) ₘ
    --     -- ·-known : ((ρ ₘ) ·ₘ (π ₘ)) ⟶ (ρ Q.· π) ₘ
    --     -- +-0ₗ : (Q.zero ₘ) +ₘ p ⟶ p  
    --     -- +-0ᵣ : p +ₘ (Q.zero ₘ) ⟶ p  
    --     -- ·-0ₗ : (Q.zero ₘ) ·ₘ p ⟶ (Q.zero ₘ)  
    --     -- ·-0ᵣ : p ·ₘ (Q.zero ₘ) ⟶ (Q.zero ₘ)

    
    -- infix 3 _↠_
    -- data _↠_ : Term n → Term n → Set where 
    --     refl-↠ : s ↠ s 
    --     trans-↠ : a ↠ b → (b⟶c : b ⟶ c) → a ↠ c   

    -- trans-↠′ : a ↠ b → b ↠ c → a ↠ c
    -- trans-↠′ a↠b refl-↠ = a↠b 
    -- trans-↠′ a↠b (trans-↠ b↠c b⟶c) = trans-↠ (trans-↠′ a↠b b↠c) b⟶c

    -- confluence-reduction : a ⟶ s → a ⟶ t → s ≡ t 
    -- confluence-reduction (β-reduce pf₁) (β-reduce pf₂) = trans pf₁ (sym pf₂)
    -- -- -- confluence-reduction +-known +-known = refl
    -- -- -- confluence-reduction (+-known {π = π}) +-0ₗ rewrite Q.+-identity π = refl
    -- -- -- confluence-reduction (+-known {ρ = ρ}) +-0ᵣ rewrite Q.+-comm ρ Q.zero rewrite Q.+-identity ρ = refl
    -- -- -- confluence-reduction ·-known ·-known = refl
    -- -- -- confluence-reduction (·-known {π = π}) ·-0ₗ rewrite Q.0-cancelₗ π = refl
    -- -- -- confluence-reduction (·-known {ρ = ρ}) ·-0ᵣ rewrite Q.0-cancelᵣ ρ = refl
    -- -- -- confluence-reduction +-0ₗ (+-known {π = π}) rewrite Q.+-identity π = refl
    -- -- -- confluence-reduction +-0ₗ +-0ₗ = refl
    -- -- -- confluence-reduction +-0ₗ +-0ᵣ = refl
    -- -- -- confluence-reduction +-0ᵣ (+-known {ρ = ρ}) rewrite Q.+-comm ρ Q.zero rewrite Q.+-identity ρ = refl
    -- -- -- confluence-reduction +-0ᵣ +-0ₗ = refl
    -- -- -- confluence-reduction +-0ᵣ +-0ᵣ = refl
    -- -- -- confluence-reduction ·-0ₗ (·-known {π = π}) rewrite Q.0-cancelₗ π = refl
    -- -- -- confluence-reduction ·-0ₗ ·-0ₗ = refl
    -- -- -- confluence-reduction ·-0ₗ ·-0ᵣ = refl
    -- -- -- confluence-reduction ·-0ᵣ (·-known {ρ = ρ}) rewrite Q.0-cancelᵣ ρ = refl
    -- -- -- confluence-reduction ·-0ᵣ ·-0ₗ = refl
    -- -- -- confluence-reduction ·-0ᵣ ·-0ᵣ = refl


        


    -- open import Data.Product
    -- open import Relation.Nullary

    -- data _▷_ : Term n → Term n → Set

    -- [_]_▷_ : (n : ℕ) → Term n → Term n → Set
    -- [ _ ] s ▷ t = s ▷ t



    -- data _▷_ where 
    --     par-star : [ n ] ⋆ ▷ ⋆ 
    --     par-mult : [ n ] mult ▷ mult 
    --     par-var : ∀ {x : n′ < n} → (` x) ▷ (` x)
    --     par-quant : [ n ] (ρ ₘ) ▷ (ρ ₘ)
    --     par-pi :
    --         p ▷ p′ → 
    --         S ▷ S′ → 
    --         T ▷ T′ → 
    --         -------------------------------------------
    --         (⦅[ p ] refl ∶ S ⦆⇒ T) ▷ (⦅[ p′ ] refl ∶ S′ ⦆⇒ T′)
    --     par-lam :
    --         p ▷ p′ → 
    --         S ▷ S′ → 
    --         b ▷ b′ → 
    --         ------------------------------------------
    --         (ƛ[ p ] refl ∶ S ⇒ b) ▷ (ƛ[ p′ ] refl ∶ S′ ⇒ b′)
    --     par-app :
    --         a ▷ a′ →
    --         b ▷ b′ →
    --         -------------------
    --         (a ∙ b) ▷ (a′ ∙ b′)
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
    --         u ≡ (beta-reduce t′ s′) →
    --         ----------------------------------------
    --         ((ƛ[ p ] refl ∶ S ⇒ t) ∙ s) ▷ u 

    -- par-refl : ∀ (a : Term n) → a ▷ a 
    -- par-refl ⋆ = par-star
    -- par-refl mult = par-mult
    -- par-refl (p +ₘ q) = par-plus (par-refl p) (par-refl q)
    -- par-refl (p ·ₘ q) = par-times (par-refl p) (par-refl q)
    -- par-refl (ρ ₘ) = par-quant 
    -- par-refl (⦅[ p ] refl ∶ A ⦆⇒ B) = par-pi (par-refl p) (par-refl A) (par-refl B)
    -- par-refl (ƛ[ p ] refl ∶ A ⇒ B) = par-lam (par-refl p) (par-refl A) (par-refl B)
    -- par-refl (` x) = par-var
    -- par-refl (s ∙ t) = par-app (par-refl s) (par-refl t) 

    -- par-refl′ : a ▷ a
    -- par-refl′ {a = a} = par-refl a

    --     {- 
    --         e ▷ e′ → t ▷ t′ → t [ e / y ] ▷ t′ [ e′ / y ]

    --     case β-reduction:
    --         a ▷ a′ , b ▷ b′
    --         t = (λx. b) a , t' = b′ [ a′ / x ] 

    --         goal:
    --         ((λx. b) a) [ e / y ] ▷ b′ [ a′ / x ] [ e′ / y ] 
    --         which if x ≠ y:
    --         (λx. b [ e / y ]) (a [ e / y ]) ▷ b′ [ a′ / x ] [ e′ / y ]
    --         otherwise:
    --         (λx. b) (a [ e / y ]) ▷ b′ [ a′ / x ] [ e′ / y ]

    --         From induction:
    --             a [ e / y ] ▷ a′ [ e′ / y ] 
    --             b [ e / y ] ▷ b′ [ e′ / y ] 
    --             b [ a / x ] ▷ b′ [ a′ / x ] 

    --         via β-reduction par rule: 

    --         for x ≠ y:
    --             (λx. b [ e / y ]) (a [ e / y ]) ▷ b′ [ e′ / y ] [ a′ [ e′ / y ] / x ]

    --         b′ [ e′ / y ] [ a′ [ e′ / y ] / x ] = b′ [ a′ / x ] [ e′ / y ]  
    --         if b′ = y: 
    --         e′ [ a′ [ e / y ] / x ] = e′  
    --         need x ∉ fvs(e′) 

    --         In terms of DeBruijn indices:

    --         our goal:
    --             ((λ0. b) a) [ e / y ] ▷ (↓₁ 0 b′ [ ↑ 1 0 a′ / 0 ]) [ e′ / y ]    

    --         induction hyps: 
    --             a [ e / y ] ▷ a′ [ e′ / y ] 
    --             b [ e / y ] ▷ b′ [ e′ / y ] 
                
    --             want to prove variant of induction hypothesis:
    --                 b [ ↑ 1 0 e / suc y ] ▷ b′ [ ↑ 1 0 e′ / suc y ] 
    --             need a lemma: e ▷ e′ → ↑ i c e ▷ ↑ i c e′  

            
    --         via β-reduction par rule:

    --             (λ0. b [ ↑ 1 0 e / suc y ]) (a [ e / y ]) ▷ ↓₁ 0 (b′ [ ↑ 1 0 e′ / suc y ] [ ↑ 1 0 (a′ [ e′ / y ]) / 0 ])

    --             thus we need:
    --             ↓₁ 0 (b′ [ ↑ 1 0 e′ / suc y ] [ ↑ 1 0 (a′ [ e′ / y ]) / 0 ]) = (↓₁ 0 (b′ [ ↑ 1 0 a′ / 0 ])) [ e′ / y ]     

    --             which should be true if (via another lemma relating ↑ and _[_‌/_]):

    --             b′ [ ↑ 1 0 e′ / suc y ] [ ((↑ 1 0 a′) [ ↑ 1 0 e′ / suc y ]) / 0 ] = b′ [ ↑ 1 0 a′ / 0 ] [ ↑ 1 0 e′ / suc y ]   

    --             which can be shown by the substitution lemma






    --     -} 