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
    open import Data.Product

    private
        variable
            k c n n′ r : ℕ
            ρ : Quant
            p q A B s t : Term n 

    -- ↑′ : (i : ℕ) → (c : ℕ) → Term n → Term (n + i)  
    -- ↑′ i c ⋆ = ⋆
    -- ↑′ i c mult = mult
    -- ↑′ i c (ρ ₘ) = ρ ₘ
    -- ↑′ i c (p +ₘ q) = (↑′ i c p) +ₘ (↑′ i c q)
    -- ↑′ i c (p ·ₘ q) = (↑′ i c p) ·ₘ (↑′ i c q)
    -- ↑′ {n} i c (⦅[ p ]∶ A ⦆⇒ B) = 
    --     ⦅[ ↑′ i c p ]∶ (↑′ i c A) ⦆⇒ ↑′ i (suc c) B 
    -- ↑′ {n} i c (ƛ[ p ]∶ A ⇒ B) = ƛ[ ↑′ i c p ]∶ (↑′ i c A) ⇒ ↑′ i (suc c) B 
    -- ↑′ i c (`_ {n′ = n′} n′<n) with n′ <? c 
    -- ... | yes _ = ` ≤-stepsʳ i n′<n  
    -- ... | no _ = ` +-monoˡ-< i n′<n 
    -- ↑′ i c (s ∙ t) = (↑′ i c s) ∙ (↑′ i c t)

    ↑ : (i : ℕ) → (c : ℕ) → Term n → Term (i + n)  
    ↑ i c ⋆ = ⋆
    ↑ i c mult = mult
    ↑ i c (ρ ₘ) = ρ ₘ 
    ↑ i c (p +ₘ q) = (↑ i c p) +ₘ (↑ i c q)
    ↑ i c (p ·ₘ q) = (↑ i c p) ·ₘ (↑ i c q)
    ↑ {n = n} i c (⦅[ p ] eq ∶ A ⦆⇒ B) = ⦅[ ↑ i c p ] (trans (cong (i +_) eq) (+-suc i n)) ∶ (↑ i c A) ⦆⇒ ↑ i (suc c) B -- ↑ i (suc c) B 
    ↑ {n = n} i c (ƛ[ p ] eq ∶ A ⇒ B) = ƛ[ ↑ i c p ] (trans (cong (i +_) eq) (+-suc i n)) ∶ (↑ i c A) ⇒ ↑ i (suc c) B -- ↑ i (suc c) B 
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
        novar-pi : NoVar n k p → NoVar n k A → (eq : n′ ≡ suc n) → NoVar n′ (suc k) B → NoVar n k (⦅[ p ] eq ∶ A ⦆⇒ B)
        novar-lam : NoVar n k p → NoVar n k A → (eq : n′ ≡ suc n) → NoVar n′ (suc k) B → NoVar n k (ƛ[ p ] eq ∶ A ⇒ B)
        novar-var : ∀ n′ → n′ ≢ k → (x : n′ < n) → NoVar n k (` x) 
        novar-app : NoVar n k s → NoVar n k t → NoVar n k (s ∙ t) 
    
    ↓₁ : ∀ {t : Term (suc n)} → (c : ℕ) → c ≤ n → NoVar (suc n) c t → Term n
    ↓₁ c c≤  novar-star = ⋆
    ↓₁ c c≤ novar-mult = mult 
    ↓₁ {t = ρ ₘ} c c≤ novar-quant = ρ ₘ 
    ↓₁ c c≤  (novar-plus nvp nvq) = ↓₁ c c≤ nvp +ₘ ↓₁ c c≤ nvq 
    ↓₁ c c≤ (novar-times nvp nvq) = ↓₁ c c≤ nvp ·ₘ ↓₁ c c≤ nvq 
    ↓₁ c c≤ (novar-pi nvp nvA refl nvB) = ⦅[ ↓₁ c c≤ nvp ] refl ∶ ↓₁ c c≤ nvA ⦆⇒ ↓₁ (suc c) (s≤s c≤) nvB
    ↓₁ c c≤ (novar-lam nvp nvA refl nvB) = ƛ[ ↓₁ c c≤ nvp ] refl ∶ ↓₁ c c≤ nvA ⇒ ↓₁ (suc c) (s≤s c≤) nvB
    ↓₁ c c≤ (novar-var n′ n′≢c (s≤s n′<n)) with n′ <? c
    ↓₁ c c≤ (novar-var n′ n′≢c (s≤s n′<n)) | yes n′<c = ` ≤-trans (≤∧≢⇒< (<⇒≤ n′<c) n′≢c) c≤
    ↓₁ c c≤ (novar-var zero n′≢c (s≤s n′<n)) | no ¬n′<c  
        with n′≥c ← ≮⇒≥ ¬n′<c
        with () ← ≤∧≢⇒< n′≥c (λ c=n → n′≢c (sym c=n))
    ↓₁ c c≤ (novar-var (suc n′) n′≢c (s≤s n′<n)) | no ¬n′<c = ` n′<n
    ↓₁ c c≤ (novar-app nvs nvt) = (↓₁ c c≤ nvs) ∙ (↓₁ c c≤ nvt) 

    _⟨_⟩[_/_] : ∀ {m} → Term n → m ≡ n → Term m → ℕ → Term n     
    ⋆ ⟨ _ ⟩[ a / k ] = ⋆
    mult ⟨ _ ⟩[ a / k ] = mult
    (ρ ₘ) ⟨ _ ⟩[ a / k ] = ρ ₘ
    (p +ₘ q) ⟨ eq ⟩[ a / k ] = (p ⟨ eq ⟩[ a / k ]) +ₘ (q ⟨ eq ⟩[ a / k ])
    (p ·ₘ q) ⟨ eq ⟩[ a / k ] = (p ⟨ eq ⟩[ a / k ]) ·ₘ (q ⟨ eq ⟩[ a / k ])
    (⦅[ p ] eq₁ ∶ A ⦆⇒ B) ⟨ eq₂ ⟩[ a / k ] = ⦅[ p ⟨ eq₂ ⟩[ a / k ] ] eq₁ ∶ A ⟨ eq₂ ⟩[ a / k ] ⦆⇒ (B ⟨ trans (cong suc eq₂) (sym eq₁) ⟩[ (↑ 1 0 a) / (suc k) ]) -- (B [ (↑ 1 0 a) / (suc k) ]) -- (B [ (↑ 1 0 a) / (suc k) ])
    (ƛ[ p ] eq₁ ∶ A ⇒ B) ⟨ eq₂ ⟩[ a / k ] = ƛ[ p ⟨ eq₂ ⟩[ a / k ] ] eq₁ ∶ A ⟨ eq₂ ⟩[ a / k ] ⇒ (B ⟨ trans (cong suc eq₂) (sym eq₁) ⟩[ (↑ 1 0 a) / (suc k) ]) -- ƛ[ p ⟨ eq₂ ⟩[ a / k ] ] ? ∶ A ⟨ eq₂ ⟩[ a / k ] ⇒ {!   !} --  (B [ subst Term (sym eq) (↑ 1 0 a) / (suc k) ])
    (`_ {n′ = x} s) ⟨ refl ⟩[ a / k ] with x ≟ k 
    ... | yes _ = a
    ... | no _ = ` s
    (s ∙ t) ⟨ eq ⟩[ a / k ] = (s ⟨ eq ⟩[ a / k ]) ∙ (t ⟨ eq ⟩[ a / k ]) 

    _[_/_] : Term n → Term n → ℕ → Term n     
    t [ a / x ] = t ⟨ refl ⟩[ a / x ]

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
    no-var-incr {n = n} {k = k} {c = c} {r = r} (⦅[ p ] refl ∶ A ⦆⇒ B) k≤c c<r = 
        let novar-B = no-var-incr B (s≤s k≤c) (subst (suc c <_) (sym $ +-suc r k) (s≤s c<r)) in
        novar-pi (no-var-incr p k≤c c<r) (no-var-incr A k≤c c<r) (+-suc r n) novar-B
    no-var-incr {n = n} {k = k} {c = c} {r = r} (ƛ[ p ] refl ∶ A ⇒ B) k≤c c<r = 
        let novar-B = no-var-incr B (s≤s k≤c) (subst (suc c <_) (sym $ +-suc r k) (s≤s c<r)) in 
        novar-lam (no-var-incr p k≤c c<r) (no-var-incr A k≤c c<r) (+-suc r n) novar-B
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
    no-var-incr-step (novar-pi nvp nvA refl nvB) k≤c = novar-pi (no-var-incr-step nvp k≤c) (no-var-incr-step nvA k≤c) refl (no-var-incr-step nvB (s≤s k≤c)) -- (no-var-incr-step nvB) 
    no-var-incr-step (novar-lam nvp nvA refl nvB) k≤c = novar-lam (no-var-incr-step nvp k≤c) (no-var-incr-step nvA k≤c) refl (no-var-incr-step nvB (s≤s k≤c)) -- (no-var-incr-step nvB) 
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
    no-var-subst (⦅[ p ] refl ∶ A ⦆⇒ B) nva = novar-pi (no-var-subst p nva) (no-var-subst A nva) refl (no-var-subst B (no-var-incr-step nva z≤n))
    no-var-subst (ƛ[ p ] refl ∶ A ⇒ B) nva = novar-lam (no-var-subst p nva) (no-var-subst A nva) refl (no-var-subst B (no-var-incr-step nva z≤n))
    no-var-subst {c = c} (`_ {n′ = x} s) nva with x ≟ c 
    ... | yes refl = nva
    ... | no x≠c = novar-var x x≠c s
    no-var-subst (s ∙ t) nva = novar-app (no-var-subst s nva) (no-var-subst t nva)

    no-var-subst-eq : ∀ a c → {t : Term n} → NoVar n c t → t [ a / c ] ≡ t
    no-var-subst-eq a c novar-star = refl
    no-var-subst-eq a c novar-mult = refl
    no-var-subst-eq a c novar-quant = refl
    no-var-subst-eq a c (novar-plus nvp nvq) 
        rewrite no-var-subst-eq a c nvp
        rewrite no-var-subst-eq a c nvq
        = refl
    no-var-subst-eq a c (novar-times nvp nvq)
        rewrite no-var-subst-eq a c nvp
        rewrite no-var-subst-eq a c nvq
        = refl 
    no-var-subst-eq a c (novar-pi nvp nvA refl nvB) 
        rewrite no-var-subst-eq a c nvp 
        rewrite no-var-subst-eq a c nvA 
        rewrite no-var-subst-eq (↑ 1 0 a) (suc c) nvB
        = refl
    no-var-subst-eq a c (novar-lam nvp nvA refl nvB) 
        rewrite no-var-subst-eq a c nvp 
        rewrite no-var-subst-eq a c nvA 
        rewrite no-var-subst-eq (↑ 1 0 a) (suc c) nvB
        = refl
    no-var-subst-eq a c (novar-var n′ n′≢c n′<c) with n′ ≟ c
    ... | yes n′≡c = contradiction n′≡c n′≢c
    ... | no _ = refl
    no-var-subst-eq a c (novar-app nvs nvt) 
        rewrite no-var-subst-eq a c nvs
        rewrite no-var-subst-eq a c nvt
        = refl

    +-injective : ∀ {i m n} → i + m ≡ i + n → m ≡ n
    +-injective {i = zero} i+m≡i+n = i+m≡i+n
    +-injective {i = suc i} i+m≡i+n = +-injective (suc-injective i+m≡i+n)

    same-pi : ∀ {n} {p A : Term n} {a} {B : Term a} (eq₁ : a ≡ suc n) (eq₂ : a ≡ suc n) → (⦅[ p ] eq₁ ∶ A ⦆⇒ B) ≡ (⦅[ p ] eq₂ ∶ A ⦆⇒ B)
    same-pi refl refl = refl

    same-lam : ∀ {n} {p A : Term n} {a} {B : Term a} (eq₁ : a ≡ suc n) (eq₂ : a ≡ suc n) → (ƛ[ p ] eq₁ ∶ A ⇒ B) ≡ (ƛ[ p ] eq₂ ∶ A ⇒ B)
    same-lam refl refl = refl

    incr-join : ∀ {i c} → (t : Term n) → ↑ 1 c (↑ i c t) ≡ ↑ (suc i) c t
    incr-join ⋆ = refl
    incr-join mult = refl
    incr-join (x ₘ) = refl
    incr-join {i = i} {c = c} (p +ₘ q) 
        rewrite incr-join {i = i} {c = c} p
        rewrite incr-join {i = i} {c = c} q
        = refl 
    incr-join {i = i} {c = c} (p ·ₘ q) 
        rewrite incr-join {i = i} {c = c} p
        rewrite incr-join {i = i} {c = c} q
        = refl
    incr-join {n = n} {i = i} {c = c} (⦅[ p ] eq ∶ A ⦆⇒ B) 
        rewrite incr-join {i = i} {c = c} p
        rewrite incr-join {i = i} {c = c} A 
        rewrite incr-join {i = i} {c = suc c} B 
        rewrite same-pi {p = ↑ (suc i) c p} {A = ↑ (suc i) c A} {B = ↑ (suc i) (suc c) B} (trans (cong (_+_ 1) (trans (cong (_+_ i) eq) (+-suc i n))) refl) (trans (cong (_+_ (suc i)) eq) (cong suc (+-suc i n))) 
        = refl 
    incr-join {n = n} {i = i} {c = c} (ƛ[ p ] eq ∶ A ⇒ B)
        rewrite incr-join {i = i} {c = c} p
        rewrite incr-join {i = i} {c = c} A 
        rewrite incr-join {i = i} {c = suc c} B 
        rewrite same-lam {p = ↑ (suc i) c p} {A = ↑ (suc i) c A} {B = ↑ (suc i) (suc c) B} (trans (cong (_+_ 1) (trans (cong (_+_ i) eq) (+-suc i n))) refl) (trans (cong (_+_ (suc i)) eq) (cong suc (+-suc i n))) 
        = refl
    incr-join {n = n} {c = c} (`_ {n′ = n′} x) with n′ <? c
    incr-join {n = n} {c = c} (`_ {n′ = n′} x) | yes _ with n′ <? c 
    incr-join {n = n} {c = c} (`_ {n′ = n′} x) | yes _  | yes _ = refl
    incr-join {n = n} {c = c} (`_ {n′ = n′} x) | yes p  | no ¬p = contradiction p ¬p
    incr-join {n = n} {i = i} {c = c} (`_ {n′ = n′} x) | no _ with i + n′ <? c 
    incr-join {n = n} {i = i} {c = c} (`_ {n′ = n′} x) | no ¬n′<c | yes i+n<c = 
        let i+sucn≤c = subst (_≤ c) (sym $ +-suc i n′) i+n<c in  
        let n′<c = m+n≤o⇒n≤o i i+sucn≤c in 
        contradiction n′<c ¬n′<c 
    incr-join {n = n} {c = c} (`_ {n′ = n′} x) | no _ | no _ = refl 
    incr-join {i = i} {c = c} (s ∙ t) 
        rewrite incr-join {i = i} {c = c} s
        rewrite incr-join {i = i} {c = c} t 
        = refl 

    -- type is wrong. not sure what right type is
    -- incr-subst : ∀ {i x} (a b : Term n) → ↑ i 0 (a [ b / x ]) ≡ (↑ i 0 a) [ ↑ i 0 b / (i + x) ]
    -- incr-subst ⋆ b = {!   !}
    -- incr-subst mult b = {!   !}
    -- incr-subst (x ₘ) b = {!   !}
    -- incr-subst (a +ₘ a₁) b = {!   !}
    -- incr-subst (a ·ₘ a₁) b = {!   !}
    -- incr-subst {i = i} {x = x} (⦅[ p ] refl ∶ A ⦆⇒ B) b 
    --     rewrite incr-subst {i = i} {x = x} p b 
    --     rewrite incr-subst {i = i} {x = x} A b 
    --     with pf ← incr-subst {i = suc i} {x = x} B (↑ 1 0 b)
    --     = {! ((⦅[ p ] eq ∶ A ⦆⇒ B) [ b / x ])  !}
    -- incr-subst (ƛ[ p ] eq ∶ A ⇒ B) b = {!   !}
    -- incr-subst {x = x} (`_ {n′ = n′} _) b with n′ ≟ x 
    -- incr-subst {x = x} (`_ {n′ = n′} _) b | yes _ with n′ <? 0 
    -- incr-subst (`_ {n′ = n′} _) b | yes refl | yes () 
    -- incr-subst {i = i} {x = x} (`_ {n′ = n′} _) b | yes _ | no ¬n′<c with i + n′ ≟ i + x 
    -- incr-subst {x = x} (`_ {n′ = n′} _) b | yes _ | no ¬n′<c | yes _ = refl
    -- incr-subst {x = x} (`_ {n′ = n′} n′<n) b | yes refl | no ¬n′<c | no i+n≢i+x = ⊥-elim (i+n≢i+x refl)
    -- incr-subst {i = i} {x = x} (`_ {n′ = n′} _) b | no _ with i + n′ ≟ i + x 
    -- incr-subst {i = i} {x = x} (`_ {n′ = n′} _) b | no n′≢x | yes i+n′≡i+x = ⊥-elim (n′≢x (+-injective i+n′≡i+x))
    -- incr-subst {i = i} {x = x} (`_ {n′ = n′} _) b | no _ | no _ = refl 
    -- incr-subst (a ∙ a₁) b = {!   !}

    subst-lemma : 
        ∀ {x y : ℕ} → {a b : Term n}
        → (t : Term n) 
        → NoVar n x b
        → x ≢ y
        → t [ b / y ] [ a [ b / y ] / x ] ≡ t [ a / x ] [ b / y ] 
    subst-lemma ⋆ nv x≢y = {!   !}
    subst-lemma mult nv x≢y = {!   !}
    subst-lemma (x ₘ) nv x≢y = {!   !}
    subst-lemma (t +ₘ t₁) nv x≢y = {!   !}
    subst-lemma (t ·ₘ t₁) nv x≢y = {!   !}
    subst-lemma {y = y} {a = a} {b = b} (⦅[ p ] refl ∶ A ⦆⇒ B) nv x≢y 
        rewrite subst-lemma {a = a} {b = b} p nv x≢y 
        rewrite subst-lemma {a = a} {b = b} A nv x≢y 
        -- rewrite incr-subst {i = 1} {x = y} a b  
        -- rewrite subst-lemma {a = ↑ 1 0 a} {b = ↑ 1 0 b} B (no-var-incr-step nv z≤n) (x≢y ∘ suc-injective) 
        = {!   !}
    subst-lemma (ƛ[ p ] refl ∶ A ⇒ B) nv x≢y = {!   !}
    subst-lemma {x = x} {y = y}  (`_ {n′ = n′} n′<c) nv x≢y with n′ ≟ y 
    subst-lemma {x = x} {y = y} (`_ {n′ = n′} n′<c) nv x≢y | yes _ with n′ ≟ x 
    subst-lemma {x = x} {y = y} (`_ {n′ = n′} n′<c) nv x≢y | yes refl | yes refl = ⊥-elim (x≢y refl)
    subst-lemma {x = x} {y = y} (`_ {n′ = n′} n′<c) nv x≢y | yes _ | no _ with n′ ≟ y
    subst-lemma {x = x} {y = y} {a = a} {b = b} (`_ {n′ = n′} n′<c) nv x≢y | yes _ | no _ | yes _ 
        rewrite no-var-subst-eq (a [ b / y ]) x nv = refl 
    subst-lemma {x = x} {y = y} (`_ {n′ = n′} n′<c) nv x≢y | yes n′≡y | no _ | no n′≢y = contradiction n′≡y n′≢y
    subst-lemma {x = x} {y = y} (`_ {n′ = n′} n′<c) nv x≢y | no _ with n′ ≟ x 
    subst-lemma {x = x} {y = y} (`_ {n′ = n′} n′<c) nv x≢y | no _ | yes _ = refl
    subst-lemma {x = x} {y = y} (`_ {n′ = n′} n′<c) nv x≢y | no _ | no _ with n′ ≟ y 
    subst-lemma {x = x} {y = y} (`_ {n′ = n′} n′<c) nv x≢y | no n′≢y | no _ | yes n′≡y = contradiction n′≡y n′≢y 
    subst-lemma {x = x} {y = y} (`_ {n′ = n′} n′<c) nv x≢y | no _ | no _ | no _ = refl
    subst-lemma {a = a} {b = b} (s ∙ t) nv x≢y 
        rewrite subst-lemma {a = a} {b = b} s nv x≢y 
        rewrite subst-lemma {a = a} {b = b} t nv x≢y = refl