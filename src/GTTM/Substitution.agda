{-# OPTIONS --allow-unsolved-metas #-}
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import GTTM.Quantity


module GTTM.Substitution (Quant : Set) (IsQuant : IsQuantity Quant) where
    open import GTTM.Syntax Quant
    open import Relation.Nullary 
    open import Relation.Nullary.Negation
    open import Data.Empty
    open import Data.Nat 
    open import Data.Nat.Properties
    open import Function.Base

    private
        variable
            k c n n′ : ℕ
            ρ : Quant
            p q A B s t : Term n 

    ↑ : (i : ℕ) → (c : ℕ) → Term n → Term (i + n)   
    ↑ i c ⋆ = ⋆
    ↑ i c mult = mult
    ↑ i c (ρ ₘ) = ρ ₘ
    ↑ i c (p +ₘ q) = (↑ i c p) +ₘ (↑ i c q)
    ↑ i c (p ·ₘ q) = (↑ i c p) ·ₘ (↑ i c q)
    ↑ {n} i c (⦅[ p ]∶ A ⦆⇒ B) = 
        ⦅[ ↑ i c p ]∶ (↑ i c A) ⦆⇒ subst Term (+-suc i n) (↑ i (suc c) B)
    ↑ {n} i c (ƛ[ p ]∶ A ⇒ B) = ƛ[ ↑ i c p ]∶ (↑ i c A) ⇒ subst Term (+-suc i n) (↑ i (suc c) B)
    ↑ i c (`_ {n′ = n′} n′<n) with n′ <? c 
    ... | yes _ = ` ≤-stepsˡ i n′<n 
    ... | no _ = ` +-monoʳ-< i n′<n
    ↑ i c (s ∙ t) = (↑ i c s) ∙ (↑ i c t)


    data NoVar : (n : ℕ) → ℕ → Term n → Set where
        novar-star : NoVar n k ⋆ 
        novar-mult : NoVar n k mult 
        novar-quant : NoVar n k (ρ ₘ) 
        novar-plus : NoVar n k p → NoVar n k q → NoVar n k (p +ₘ q) 
        novar-times : NoVar n k p → NoVar n k q → NoVar n k (p ·ₘ q) 
        novar-pi : NoVar n k p → NoVar n k A → NoVar (suc n) (suc k) B → NoVar n k (⦅[ p ]∶ A ⦆⇒ B)
        novar-lam : NoVar n k p → NoVar n k A → NoVar (suc n) (suc k) B → NoVar n k (ƛ[ p ]∶ A ⇒ B)
        novar-var : ∀ n′ → n′ ≢ k → (x : n′ < n) → NoVar n k (` x) 
        novar-app : NoVar n k s → NoVar n k t → NoVar n k (s ∙ t) 
    
    ↓₁ : ∀ {t : Term (suc n)} → (c : ℕ) → c < (suc n) → NoVar (suc n) c t → Term n
    ↓₁ c c≤  novar-star = ⋆
    ↓₁ c c≤ novar-mult = mult 
    ↓₁ {t = ρ ₘ} c c≤ novar-quant = ρ ₘ 
    ↓₁ c c≤  (novar-plus nvp nvq) = ↓₁ c c≤ nvp +ₘ ↓₁ c c≤ nvq 
    ↓₁ c c≤ (novar-times nvp nvq) = ↓₁ c c≤ nvp ·ₘ ↓₁ c c≤ nvq 
    ↓₁ c c≤ (novar-pi nvp nvA nvB) = ⦅[ ↓₁ c c≤ nvp ]∶ ↓₁ c c≤ nvA ⦆⇒ ↓₁ (suc c) (s≤s c≤) nvB
    ↓₁ c c≤ (novar-lam nvp nvA nvB) = ƛ[ ↓₁ c c≤ nvp ]∶ ↓₁ c c≤ nvA ⇒ ↓₁ (suc c) (s≤s c≤) nvB
    ↓₁ c (s≤s c≤) (novar-var n′ n′≢c (s≤s n′<n)) with n′ <? c
    ↓₁ c (s≤s c≤) (novar-var n′ n′≢c (s≤s n′<n)) | yes n′<c = ` ≤-trans (≤∧≢⇒< (<⇒≤ n′<c) n′≢c) c≤
    ↓₁ c (s≤s c≤) (novar-var zero n′≢c (s≤s n′<n)) | no ¬n′<c  
        with n′≥c ← ≮⇒≥ ¬n′<c
        with () ← ≤∧≢⇒< n′≥c (λ c=n → n′≢c (sym c=n))
    ↓₁ c (s≤s c≤) (novar-var (suc n′) n′≢c (s≤s n′<n)) | no ¬n′<c = ` n′<n
    ↓₁ c c≤ (novar-app nvs nvt) = (↓₁ c c≤ nvs) ∙ (↓₁ c c≤ nvt) 

    _[_/_] : Term n → Term n → ℕ → Term n     
    ⋆ [ a / k ] = ⋆
    mult [ a / k ] = mult
    (ρ ₘ) [ a / k ] = ρ ₘ
    (p +ₘ q) [ a / k ] = (p [ a / k ]) +ₘ (q [ a / k ])
    (p ·ₘ q) [ a / k ] = (p [ a / k ]) ·ₘ (q [ a / k ])
    (⦅[ p ]∶ A ⦆⇒ B) [ a / k ] = ⦅[ p [ a / k ] ]∶ A [ a / k ] ⦆⇒ (B [ ↑ 1 0 a / (suc k) ])
    (ƛ[ p ]∶ A ⇒ B) [ a / k ] = ƛ[ p [ a / k ] ]∶ A [ a / k ] ⇒ (B [ ↑ 1 0 a / (suc k) ])
    (`_ {n′ = x} s) [ a / k ] with x ≟ k 
    ... | yes _ = a
    ... | no _ = ` s
    (s ∙ t) [ a / k ] = (s [ a / k ]) ∙ (t [ a / k ]) 