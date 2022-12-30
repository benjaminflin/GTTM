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
            k c n n′ r : ℕ
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

    m<n⇒m≢n : ∀ {m n} → m < n → m ≢ n 
    m<n⇒m≢n {m} {n} m<n refl = n≮n m m<n

    subst-eq-novar : ∀ {a b c : ℕ} {t : Term a} → (eq : a ≡ b) → NoVar a c t → NoVar b c (subst Term eq t) 
    subst-eq-novar refl nv = nv 

    no-var-incr : (t : Term n) → k ≤ c → c < r + k → NoVar (r + n) c (↑ r k t)    
    no-var-incr ⋆ k≤c c<r = novar-star
    no-var-incr mult k≤c c<r = novar-mult
    no-var-incr (_ ₘ) k≤c c<r = novar-quant
    no-var-incr (p +ₘ q) k≤c c<r = novar-plus (no-var-incr p k≤c c<r) (no-var-incr q k≤c c<r)
    no-var-incr (p ·ₘ q) k≤c c<r = novar-times (no-var-incr p k≤c c<r) (no-var-incr q k≤c c<r)
    no-var-incr {n = n} {k = k} {c = c} {r = r} (⦅[ p ]∶ A ⦆⇒ B) k≤c c<r = 
        let novar-B = no-var-incr B (s≤s k≤c) (subst (suc c <_) (sym $ +-suc r k) (s≤s c<r)) in
        novar-pi (no-var-incr p k≤c c<r) (no-var-incr A k≤c c<r) (subst-eq-novar (+-suc r n) novar-B)
    no-var-incr {n = n} {k = k} {c = c} {r = r} (ƛ[ p ]∶ A ⇒ B) k≤c c<r = 
        let novar-B = no-var-incr B (s≤s k≤c) (subst (suc c <_) (sym $ +-suc r k) (s≤s c<r)) in
        novar-lam (no-var-incr p k≤c c<r) (no-var-incr A k≤c c<r) (subst-eq-novar (+-suc r n) novar-B) 
    no-var-incr {n = n} {k = k} {c = c} {r = r} (`_ {n′ = n′} x) k≤c c<r with n′ <? k 
    ... | yes n′<k = novar-var n′ (m<n⇒m≢n (<-transˡ n′<k k≤c)) (≤-stepsˡ r x)
    ... | no ¬n′<k with n′≥k ← ≮⇒≥ ¬n′<k rewrite +-suc r n′ = 
        conv $ novar-var (r + n′) (m<n⇒m≢n (<-transˡ c<r (+-monoʳ-≤ r n′≥k)) ∘ sym) (subst (_≤ r + n) (+-suc r n′) (+-monoʳ-≤ r x))
        where
            ≤-lem : ∀ {a b : ℕ} (lt₁ : a ≤ b) (lt₂ : a ≤ b) → lt₁ ≡ lt₂ 
            ≤-lem z≤n z≤n = refl
            ≤-lem (s≤s lt₁) (s≤s lt₂) = cong (s≤s) (≤-lem lt₁ lt₂)

            conv : ∀ {n c a} {x y : a < n} → NoVar n c (` x) → NoVar n c (` y)  
            conv {x = x} {y = y} nv rewrite ≤-lem x y = nv  
    no-var-incr (s ∙ t) k≤c c<r = novar-app (no-var-incr s k≤c c<r) (no-var-incr t k≤c c<r)

    no-var-incr-step : ∀ {t : Term n} → NoVar n c t → k ≤ suc c → NoVar (suc n) (suc c) (↑ 1 k t)
    no-var-incr-step novar-star k≤c = novar-star
    no-var-incr-step novar-mult k≤c = novar-mult
    no-var-incr-step novar-quant k≤c = novar-quant
    no-var-incr-step (novar-plus nvp nvq) k≤c = novar-plus (no-var-incr-step nvp k≤c) (no-var-incr-step nvq k≤c) 
    no-var-incr-step (novar-times nvp nvq) k≤c = novar-times (no-var-incr-step nvp k≤c) (no-var-incr-step nvq k≤c) 
    no-var-incr-step (novar-pi nvp nvA nvB) k≤c = novar-pi (no-var-incr-step nvp k≤c) (no-var-incr-step nvA k≤c) (no-var-incr-step nvB (s≤s k≤c)) -- (no-var-incr-step nvB) 
    no-var-incr-step (novar-lam nvp nvA nvB) k≤c = novar-lam (no-var-incr-step nvp k≤c) (no-var-incr-step nvA k≤c) (no-var-incr-step nvB (s≤s k≤c)) -- (no-var-incr-step nvB) 
    no-var-incr-step {k = k} (novar-var n′ n′≢c x) k≤c with n′ <? k 
    ... | yes n′<k = novar-var n′ (m<n⇒m≢n (≤-trans n′<k k≤c)) (≤-step x) 
    ... | no n′>k = novar-var (suc n′) (n′≢c ∘ suc-injective) (s≤s x) 
    no-var-incr-step (novar-app nvs nvt) k≤c = novar-app (no-var-incr-step nvs k≤c) (no-var-incr-step nvt k≤c)


    no-var-subst : ∀ {a} → (t : Term n) → NoVar n c a → NoVar n c (t [ a / c ])
    no-var-subst ⋆ nva = novar-star
    no-var-subst mult nva = novar-mult
    no-var-subst (x ₘ) nva = novar-quant
    no-var-subst (p +ₘ q) nva = novar-plus (no-var-subst p nva) (no-var-subst q nva)
    no-var-subst (p ·ₘ q) nva = novar-times (no-var-subst p nva) (no-var-subst q nva) 
    no-var-subst (⦅[ p ]∶ A ⦆⇒ B) nva = novar-pi (no-var-subst p nva) (no-var-subst A nva) (no-var-subst B (no-var-incr-step nva z≤n))
    no-var-subst (ƛ[ p ]∶ A ⇒ B) nva = novar-lam (no-var-subst p nva) (no-var-subst A nva) (no-var-subst B (no-var-incr-step nva z≤n))
    no-var-subst {c = c} (`_ {n′ = x} s) nva with x ≟ c 
    ... | yes refl = nva
    ... | no x≠c = novar-var x x≠c s
    no-var-subst (s ∙ t) nva = novar-app (no-var-subst s nva) (no-var-subst t nva)

