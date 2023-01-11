{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import GTTM.Quantity


module GTTM.Substitution (Quant : Set) (IsQuant : IsQuantity Quant) where
    open import GTTM.Syntax Quant
    open import Relation.Nullary 
    open import Relation.Nullary.Negation
    open import Data.Empty
    open import Data.Nat 
    open import Data.Nat.Properties
    open import Function.Base
    open import Data.Product

    open ≡-Reasoning

    private
        variable
            x m k c n n′ r : ℕ
            ρ : Quant
            p q A B s t : Term
        
        postulate
            extensionality : 
                ∀ {A B : Set} {f g : A → B}
                → (∀ (x : A) → f x ≡ g x)
                → f ≡ g


    Subst : Set
    Subst = ℕ → Term    

    Renaming : Set
    Renaming = ℕ → ℕ 

    _·_ : Term → Subst → Subst    
    (s · σ) zero = s
    (s · σ) (suc x) = σ x

    ids : Subst 
    ids x = ` x

    ren : Renaming → Subst
    ren ξ = ids ∘ ξ   

    ↑ : Subst
    ↑ x = ` suc x 

    ext : Renaming → Renaming
    ext ξ zero = zero
    ext ξ (suc x) = suc (ξ x)

    rename : Renaming → Term → Term
    rename ξ ⋆ = ⋆
    rename ξ mult = mult
    rename ξ (ρ ₘ) = ρ ₘ
    rename ξ (p ⟪ b ⟫ q) = (rename ξ p) ⟪ b ⟫ (rename ξ q)
    rename ξ (b ⟦ p ⟧∶ A ⇒ B) = b ⟦ rename ξ p ⟧∶ rename ξ A ⇒ (rename (ext ξ) B)
    rename ξ (` x) = ` ξ x
    rename ξ (s ∙ t) = rename ξ s ∙ rename ξ t  

    ⇑ : Subst → Subst
    ⇑ σ zero = ` 0
    ⇑ σ (suc x) = rename suc (σ x) 

    _>>_ : Subst → Subst → Subst
    _[_] : Term → Subst → Term

    (σ >> τ) x = (σ x) [ τ ]

    ⋆ [ σ ] = ⋆
    mult [ σ ] = mult
    (ρ ₘ) [ σ ] = ρ ₘ
    (p ⟪ b ⟫ q) [ σ ] = (p [ σ ]) ⟪ b ⟫ (q [ σ ])
    (b ⟦ p ⟧∶ A ⇒ B) [ σ ] = b ⟦ p [ σ ] ⟧∶ (A [ σ ]) ⇒ (B [ ⇑ σ ])
    (` x) [ σ ] = σ x
    (s ∙ t) [ σ ] = (s [ σ ]) ∙ (t [ σ ]) 


    sub-head : ∀ t σ → (` 0) [ t · σ ] ≡ t 
    sub-head t σ = refl

    sub-tail : ∀ t σ → (↑ >> (t · σ)) ≡ σ
    sub-tail t σ = extensionality λ x → refl

    sub-η : ∀ σ → ((` 0) [ σ ]) · (↑ >> σ) ≡ σ  
    sub-η σ = extensionality lem 
        where
        lem : ∀ x → (((` 0) [ σ ]) · (↑ >> σ)) x ≡ σ x
        lem zero = refl
        lem (suc x) = refl

    z-shift : (` 0) · ↑ ≡ ids  
    z-shift = extensionality lem 
        where
        lem : ∀ x → ((` 0) · ↑) x ≡ ids x
        lem zero = refl
        lem (suc x) = refl

    sub-idL : ∀ σ → ids >> σ ≡ σ 
    sub-idL σ = extensionality λ x → refl

    sub-dist : ∀ σ σ′ t → (t · σ) >> σ′ ≡ (t [ σ′ ]) · (σ >> σ′)
    sub-dist σ σ′ t = extensionality lem
        where
        lem : ∀ x → ((t · σ) >> σ′) x ≡ ((t [ σ′ ]) · (σ >> σ′)) x
        lem zero = refl
        lem (suc x) = refl

    ren-ext : ∀ ξ → ren (ext ξ) ≡ ⇑ (ren ξ)     
    ren-ext ξ = extensionality lem 
        where
        lem : ∀ x → ren (ext ξ) x ≡ ⇑ (ren ξ) x
        lem zero = refl
        lem (suc x) = refl

    rename-subst-ren : ∀ ξ t → rename ξ t ≡ t [ ren ξ ]  
    rename-subst-ren ξ ⋆ = refl
    rename-subst-ren ξ mult = refl
    rename-subst-ren ξ (x ₘ) = refl
    rename-subst-ren ξ (p ⟪ b ⟫ q) = cong₂ _⟪ b ⟫_ (rename-subst-ren ξ p) (rename-subst-ren ξ q)
    rename-subst-ren ξ (b ⟦ p ⟧∶ A ⇒ B) = 
        begin
            (b ⟦ rename ξ p ⟧∶ rename ξ A ⇒ rename (ext ξ) B)
        ≡⟨ cong₂ (λ p A → b ⟦ p ⟧∶ A ⇒ rename (ext ξ) B) (rename-subst-ren ξ p) (rename-subst-ren ξ A) ⟩
            (b ⟦ p [ ren ξ ] ⟧∶ A [ ren ξ ] ⇒ rename (ext ξ) B)
        ≡⟨ cong (λ B → b ⟦ p [ ren ξ ] ⟧∶ A [ ren ξ ] ⇒ B) (rename-subst-ren (ext ξ) B) ⟩
            (b ⟦ p [ ren ξ ] ⟧∶ A [ ren ξ ] ⇒ (B [ ren (ext ξ) ]))
        ≡⟨ cong (λ σ → b ⟦ p [ ren ξ ] ⟧∶ A [ ren ξ ] ⇒ (B [ σ ])) (ren-ext ξ) ⟩
            (b ⟦ p [ ren ξ ] ⟧∶ A [ ren ξ ] ⇒ (B [ ⇑ (ren ξ) ]))
       ∎ 
    rename-subst-ren ξ (` x) = refl
    rename-subst-ren ξ (s ∙ t) = cong₂ _∙_ (rename-subst-ren ξ s) (rename-subst-ren ξ t) 

    ren-shift : ren suc ≡ ↑  
    ren-shift = extensionality lem 
        where
        lem : ∀ x → ren suc x ≡ ↑ x 
        lem zero = refl
        lem (suc x) = refl

    rename-shift : ∀ t → rename suc t ≡ t [ ↑ ]
    rename-shift t = 
        begin
            rename suc t
        ≡⟨ rename-subst-ren suc t ⟩
            t [ ren suc ]
        ≡⟨ cong (λ σ → t [ σ ]) ren-shift ⟩
            t [ ↑ ]
        ∎
    
    ext-cons-shift : ∀ σ → ⇑ σ ≡ ((` 0) · (σ >> ↑))
    ext-cons-shift σ = extensionality lem
        where
        lem : ∀ x → ⇑ σ x ≡ ((` 0) · (σ >> ↑)) x
        lem zero = refl
        lem (suc x) = rename-subst-ren suc (σ x)


    sub-bind : ∀ p A B b σ → ((b ⟦ p ⟧∶ A ⇒ B) [ σ ]) ≡ (b ⟦ p [ σ ] ⟧∶ A [ σ ] ⇒ (B [ (` 0) · (σ >> ↑) ]))
    sub-bind p A B b σ = cong (λ σ′ → b ⟦ p [ σ ] ⟧∶ A [ σ ] ⇒ (B [ σ′ ])) (ext-cons-shift σ)

    ⇑-ids : ⇑ ids ≡ ids  
    ⇑-ids = extensionality lem 
        where
        lem : ∀ x → ⇑ ids x ≡ ids x 
        lem zero = refl
        lem (suc x) = refl
    

    sub-id : ∀ t → t [ ids ] ≡ t
    sub-id ⋆ = refl
    sub-id mult = refl
    sub-id (x ₘ) = refl
    sub-id (p ⟪ b ⟫ q) = cong₂ _⟪ b ⟫_ (sub-id p) (sub-id q)  
    sub-id (b ⟦ p ⟧∶ A ⇒ B) = 
        begin
            b ⟦ p [ ids ] ⟧∶ (A [ ids ]) ⇒ (B [ ⇑ ids ])
        ≡⟨ cong₂ (λ p A → b ⟦ p ⟧∶ A ⇒ (B [ ⇑ ids ])) (sub-id p) (sub-id A) ⟩
            b ⟦ p ⟧∶ A ⇒ (B [ ⇑ ids ])
        ≡⟨ cong (λ σ → b ⟦ p ⟧∶ A ⇒ (B [ σ ])) ⇑-ids  ⟩
            b ⟦ p ⟧∶ A ⇒ (B [ ids ])
        ≡⟨ cong (λ B → b ⟦ p ⟧∶ A ⇒ B) (sub-id B) ⟩
            b ⟦ p ⟧∶ A ⇒ B
        ∎  
    sub-id (` x) = refl
    sub-id (s ∙ t) = cong₂ _∙_ (sub-id s) (sub-id t)

    rename-id : ∀ t → rename id t ≡ t      
    rename-id t = 
        begin
            rename id t
        ≡⟨ rename-subst-ren id t ⟩
            t [ ren id ]  
        ≡⟨ sub-id t ⟩
            t
        ∎ 
    
    sub-idR : ∀ σ → σ >> ids ≡ σ    
    sub-idR σ = 
        begin
            σ >> ids 
        ≡⟨ refl ⟩
            (λ t → (σ t) [ ids ])
        ≡⟨ extensionality (λ x → sub-id (σ x)) ⟩ 
            σ 
        ∎
    
    compose-ext : ∀ ξ ξ′ → ext ξ ∘ ext ξ′ ≡ ext (ξ ∘ ξ′) 
    compose-ext ξ ξ′ = extensionality lem
        where
        lem : ∀ x → (ext ξ ∘ ext ξ′) x ≡ ext (ξ ∘ ξ′) x
        lem zero = refl
        lem (suc x) = refl
    
    compose-rename : ∀ ξ ξ′ t → (rename ξ ∘ rename ξ′) t ≡ rename (ξ ∘ ξ′) t  
    compose-rename ξ ξ′ ⋆ = refl
    compose-rename ξ ξ′ mult = refl
    compose-rename ξ ξ′ (ρ ₘ) = refl
    compose-rename ξ ξ′ (p ⟪ b ⟫ q) = cong₂ _⟪ b ⟫_ (compose-rename ξ ξ′ p) (compose-rename ξ ξ′ q)
    compose-rename ξ ξ′ (b ⟦ p ⟧∶ A ⇒ B) = 
        begin
            (rename ξ ∘ rename ξ′) (b ⟦ p ⟧∶ A ⇒ B)
        ≡⟨ cong₂ (λ p A → b ⟦ p ⟧∶ A ⇒ rename (ext ξ) (rename (ext ξ′) B)) (compose-rename ξ ξ′ p) (compose-rename ξ ξ′ A) ⟩
            b ⟦ rename (ξ ∘ ξ′) p ⟧∶ (rename (ξ ∘ ξ′) A) ⇒ rename (ext ξ) (rename (ext ξ′) B) 
        ≡⟨ cong (λ B → b ⟦ rename (ξ ∘ ξ′) p ⟧∶ rename (ξ ∘ ξ′) A ⇒ B) (compose-rename (ext ξ) (ext ξ′) B) ⟩
            b ⟦ rename (ξ ∘ ξ′) p ⟧∶ (rename (ξ ∘ ξ′) A) ⇒ (rename ((ext ξ) ∘ (ext ξ′)) B)
        ≡⟨ cong (λ B → b ⟦ rename (ξ ∘ ξ′) p ⟧∶ rename (ξ ∘ ξ′) A ⇒ B) (cong (λ ξ → rename ξ B) (compose-ext ξ ξ′)) ⟩
            b ⟦ rename (ξ ∘ ξ′) p ⟧∶ rename (ξ ∘ ξ′)  A ⇒ rename (ext (ξ ∘ ξ′)) B
        ∎
    compose-rename ξ ξ′ (` x) = refl
    compose-rename ξ ξ′ (s ∙ t) = cong₂ _∙_ (compose-rename ξ ξ′ s) (compose-rename ξ ξ′ t) 

    commute-subst-rename : ∀ σ ξ t → (∀ x → ⇑ σ (ξ x) ≡ rename ξ (σ x)) → (rename ξ t) [ ⇑ σ ] ≡ rename ξ (t [ σ ]) 
    commute-subst-rename σ ξ ⋆ cv = refl
    commute-subst-rename σ ξ mult cv = refl
    commute-subst-rename σ ξ (x ₘ) cv = refl
    commute-subst-rename σ ξ (p ⟪ x ⟫ q) cv = cong₂ _⟪ x ⟫_ (commute-subst-rename σ ξ p cv) (commute-subst-rename σ ξ q cv)
    commute-subst-rename σ ξ (b ⟦ p ⟧∶ A ⇒ B) cv = 
        begin
            (b ⟦ rename ξ p [ ⇑ σ ] ⟧∶ rename ξ A [ ⇑ σ ] ⇒ (rename (ext ξ) B [ ⇑ (⇑ σ) ]))
        ≡⟨ cong₂ (λ p A → b ⟦ p ⟧∶ A ⇒ (rename (ext ξ) B [ ⇑ (⇑ σ) ])) (commute-subst-rename σ ξ p cv) (commute-subst-rename σ ξ A cv) ⟩
            (b ⟦ rename ξ (p [ σ ]) ⟧∶ rename ξ (A [ σ ]) ⇒ (rename (ext ξ) B [ ⇑ (⇑ σ) ]))
        ≡⟨ cong (λ B → (b ⟦ rename ξ (p [ σ ]) ⟧∶ rename ξ (A [ σ ]) ⇒ B)) (commute-subst-rename (⇑ σ) (ext ξ) B lem) ⟩
            (b ⟦ rename ξ (p [ σ ]) ⟧∶ rename ξ (A [ σ ]) ⇒ rename (ext ξ) (B [ ⇑ σ ]))
        ∎
        where
        lem : ∀ x → ⇑ (⇑ σ) (ext ξ x) ≡ rename (ext ξ) (⇑ σ x)
        lem zero = refl
        lem (suc x) = 
            begin
                ⇑ (⇑ σ) (ext ξ (suc x))
            ≡⟨ refl ⟩ 
                rename suc (⇑ σ (ξ x))  
            ≡⟨ cong (rename suc) (cv x) ⟩ 
                rename suc (rename ξ (σ x))
            ≡⟨ compose-rename suc ξ (σ x) ⟩ 
                rename (suc ∘ ξ) (σ x)
            ≡⟨ cong (λ ξ → rename ξ (σ x)) refl ⟩
                rename ((ext ξ) ∘ suc) (σ x)
            ≡⟨ sym (compose-rename (ext ξ) suc (σ x)) ⟩
                rename (ext ξ) (rename suc (σ x))
            ∎
    commute-subst-rename σ ξ (` x) cv = cv x
    commute-subst-rename σ ξ (s ∙ t) cv = cong₂ _∙_ (commute-subst-rename σ ξ s cv) (commute-subst-rename σ ξ t cv)

    ⇑-seq : ∀ σ σ′ → ⇑ σ >> ⇑ σ′ ≡ ⇑ (σ >> σ′) 
    ⇑-seq σ σ′ = extensionality lem 
        where
        lem : ∀ x → (⇑ σ >> ⇑ σ′) x ≡ (⇑ (σ >> σ′)) x
        lem zero = refl
        lem (suc x) = 
            begin 
                (⇑ σ >> ⇑ σ′) (suc x)
            ≡⟨ refl ⟩
                rename suc (σ x) [ ⇑ σ′ ]
            ≡⟨ commute-subst-rename σ′ suc (σ x) (λ x → refl) ⟩
                rename suc (σ x [ σ′ ])
            ≡⟨ refl ⟩
                (⇑ (σ >> σ′)) (suc x)
            ∎
        
    sub-sub : ∀ σ σ′ t → t [ σ ] [ σ′ ] ≡ t [ σ >> σ′ ]  
    sub-sub σ σ′ ⋆ = refl
    sub-sub σ σ′ mult = refl
    sub-sub σ σ′ (x ₘ) = refl
    sub-sub σ σ′ (p ⟪ b ⟫ q) = cong₂ _⟪ b ⟫_ (sub-sub σ σ′ p) (sub-sub σ σ′ q)
    sub-sub σ σ′ (b ⟦ p ⟧∶ A ⇒ B) = 
        begin
            (b ⟦ (p [ σ ]) [ σ′ ] ⟧∶ (A [ σ ]) [ σ′ ] ⇒ ((B [ ⇑ σ ]) [ ⇑ σ′ ]))
        ≡⟨ cong₂ (λ p A → b ⟦ p ⟧∶ A ⇒ ((B [ ⇑ σ ]) [ ⇑ σ′ ])) (sub-sub σ σ′ p) (sub-sub σ σ′ A) ⟩ 
            (b ⟦ p [ σ >> σ′ ] ⟧∶ A [ σ >> σ′ ] ⇒ ((B [ ⇑ σ ]) [ ⇑ σ′ ]))
        ≡⟨ cong (λ B → b ⟦ p [ σ >> σ′ ] ⟧∶ A [ σ >> σ′ ] ⇒ B) (sub-sub (⇑ σ) (⇑ σ′) B) ⟩ 
            (b ⟦ p [ σ >> σ′ ] ⟧∶ A [ σ >> σ′ ] ⇒ (B [ ⇑ σ >> ⇑ σ′ ]))
        ≡⟨ cong (λ B → b ⟦ p [ σ >> σ′ ] ⟧∶ A [ σ >> σ′ ] ⇒ B) (cong (B [_]) (⇑-seq σ σ′)) ⟩
            (b ⟦ p [ σ >> σ′ ] ⟧∶ A [ σ >> σ′ ] ⇒ (B [ ⇑ (σ >> σ′) ]))
        ∎
    sub-sub σ σ′ (` x) = refl
    sub-sub σ σ′ (s ∙ t) = cong₂ _∙_ (sub-sub σ σ′ s) (sub-sub σ σ′ t)

    sub-assoc : ∀ σ₁ σ₂ σ₃ → (σ₁ >> σ₂) >> σ₃ ≡ σ₁ >> (σ₂ >> σ₃)
    sub-assoc σ₁ σ₂ σ₃ = extensionality lem  
        where
        lem : ∀ x → ((σ₁ >> σ₂) >> σ₃) x ≡ (σ₁ >> (σ₂ >> σ₃)) x
        lem x = 
            begin
                ((σ₁ x [ σ₂ ]) [ σ₃ ])
            ≡⟨ sub-sub σ₂ σ₃ (σ₁ x) ⟩
                (σ₁ x [ σ₂ >> σ₃ ])
            ∎


    subst-lemma : ∀ σ s t → s [ ⇑ σ ] [ (t [ σ ]) · ids ] ≡ s [ t · ids ] [ σ ]
    subst-lemma σ s t = 
        begin
            (s [ ⇑ σ ]) [ (t [ σ ]) · ids ]
        ≡⟨ sub-sub (⇑ σ) ((t [ σ ]) · ids) s ⟩
            s [ ⇑ σ >> ((t [ σ ]) · ids) ] 
        ≡⟨ cong (s [_]) (cong₂ (_>>_) (ext-cons-shift σ) refl) ⟩
            s [ ((` 0) · (σ >> ↑)) >> ((t [ σ ]) · ids) ]
        ≡⟨ cong (s [_]) (sub-dist (σ >> ↑) ((t [ σ ]) · ids) (` 0)) ⟩
            s [ (t [ σ ]) · ((σ >> ↑) >> ((t [ σ ]) · ids)) ]
        ≡⟨ cong (λ τ → s [ (t [ σ ]) · τ ]) (sub-assoc σ ↑ ((t [ σ ]) · ids)) ⟩
            s [ (t [ σ ]) · (σ >> (↑ >> ((t [ σ ]) · ids))) ]
        ≡⟨ refl ⟩
            (s [ (t [ σ ]) · (σ >> ids) ])
        ≡⟨ cong (λ τ → s [ (t [ σ ]) · τ ]) (sub-idR σ) ⟩
            (s [ (t [ σ ]) · σ ])
        ≡⟨ refl ⟩
            (s [ (t [ σ ]) · (ids >> σ) ])
        ≡⟨ cong (s [_]) (sym (sub-dist ids σ t)) ⟩
            (s [ (t · ids) >> σ ])
        ≡⟨ sym (sub-sub (t · ids) σ s) ⟩
            (s [ t · ids ]) [ σ ]
        ∎

