# A Usage Aware Graded Dependent Type System with First Class Multiplicites

## Abstract

Graded Type Theory (GTT) by allows resource tracking
by annotation binders with a grade semiring, enabling
a resource tracking of variable usage similar to linear logic.
We describe an extended GTT with first class grades and 
prove progress, preservation, confluence and heap-preservation
properties for this system. This paper is typecheckable as a 
literate agda file.

```agda
module GTTM where 

open import Relation.Binary.PropositionalEquality

```

## Quantities

Quantities are semirings (Q,+,·,0,1) with an ordering relation (≤).

```agda
record IsQuantity (Q : Set) : Set₁ where 
    infixl 5 _+_ 
    infixl 7 _·_ 
    infix 2 _≤_
    field
        zero : Q
        one : Q
        _+_ : Q → Q → Q
        _·_ : Q → Q → Q 
        _≤_ : Q → Q → Set
        +-identity : ∀ ρ → zero + ρ ≡ ρ 
        +-assoc : ∀ ρ π ϕ → ρ + (π + ϕ) ≡ (ρ + π) + ϕ
        +-comm : ∀ ρ π → ρ + π ≡ π + ρ 
        ·-assoc : ∀ ρ π ϕ → ρ · (π · ϕ) ≡ (ρ · π) · ϕ
        -- Are these actually necessary for the theory? 
        -- It would be nice if quantities could have 0 = 1 in a non-trivial way
        -- ·-identityₗ : ∀ ρ → one · ρ ≡ ρ 
        -- ·-identityᵣ : ∀ ρ → ρ · one ≡ ρ 
        0-cancelₗ : ∀ ρ → zero · ρ ≡ zero 
        0-cancelᵣ : ∀ ρ → ρ · zero ≡ zero 
        ·-+-distributiveₗ : ∀ ϕ ρ π → ϕ · (ρ + π) ≡ ϕ · ρ + ϕ · π         
        ·-+-distributiveᵣ : ∀ ϕ ρ π → (ρ + π) · ϕ ≡ ρ · ϕ + π · ϕ
        ≤-refl : ∀ ρ → ρ ≤ ρ
        -- might also not be needed
        -- ≤-irrefl : ∀ ρ π → ρ ≤ π → π ≤ ρ → ρ ≡ π
        ≤-trans : ∀ ρ π ϕ → ρ ≤ π → π ≤ ϕ → ρ ≤ ϕ
        ≤-+ : ∀ ρ π ϕ → ρ ≤ π → ρ + ϕ ≤ π + ϕ
        ≤-·ₗ : ∀ ρ π ϕ → ρ ≤ π → ϕ · ρ ≤ ϕ · π 
        ≤-·ᵣ : ∀ ρ π ϕ → ρ ≤ π → ρ · ϕ ≤ π · ϕ
```


```agda
module Syntax (Var : Set) (Quant : Set) where 

    data Term : Set 

    Type : Set
    Type = Term

    data Term where
        ⋆ : Type 
        mult : Type 
        _+ₘ_ : Term → Term → Term
        _·ₘ_ : Term → Term → Term
        _ₘ : Quant → Term 
        ⦅[_]_∶_⦆⇒_ : Term → Var → Type → Type → Type 
        ƛ[_]_∶_⇒_ : Term → Var → Type → Term → Term 
        `_ : Var → Term 
        _∙_ : Term → Term → Term
    
```

```agda
open import Relation.Binary

module Context (Var : Set) (Quant : Set) (IsQuant : IsQuantity Quant) where 

    open Syntax Var Quant

    data PreContext : Set where
        ∅ₚ : PreContext
        _,_∶_ : PreContext → Var → Type → PreContext

    data Context : Set where 
        ∅ : Context 
        _,[_]_∶_ : Context → Term → Var → Type → Context

    private
        variable
            x y : Var
            p q r s t : Term
            S T A B : Type
            Γ Γ₁ Γ₂ Δ : Context

    data [_]_∶_∈_ : Term → Var → Type → Context → Set where
        here : [ p ] x ∶ T ∈ (Γ ,[ p ] x ∶ T)
        there : [ p ] x ∶ T ∈ Γ → x ≢ y → [ p ] x ∶ T ∈ (Γ ,[ q ] y ∶ S)

    ⌊_⌋ : Context → PreContext
    ⌊ ∅ ⌋ = ∅ₚ
    ⌊ Δ ,[ q ] v ∶ t ⌋ = ⌊ Δ ⌋ , v ∶ t 

    infix 10 _·_
    _·_ : Term → Context → Context
    p · ∅ = ∅
    p · (Γ ,[ q ] t ∶ T) = (p · Γ) ,[ p ·ₘ q ] t ∶ T

    open IsQuantity IsQuant using (zero)

    infix 50 𝟘_
    𝟘_ : Context → Context 
    𝟘 ∅ = ∅
    𝟘 (Γ ,[ p ] x ∶ T) = 𝟘 Γ ,[ zero ₘ ] x ∶ T

    𝟘-idempotent : ∀ Γ → 𝟘 (𝟘 Γ) ≡ 𝟘 Γ
    𝟘-idempotent ∅ = refl
    𝟘-idempotent (Γ ,[ p ] x ∶ T) = cong (_,[ zero ₘ ] x ∶ T) (𝟘-idempotent Γ)


    data [_]_∶_∈₀_ : Term → Var → Type → Context → Set where
        here₀ : 𝟘 Γ ≡ Γ → [ p ] x ∶ T ∈₀ (Γ ,[ p ] x ∶ T)
        there₀ : [ p ] x ∶ T ∈₀ Γ → x ≢ y → [ p ] x ∶ T ∈₀ (Γ ,[ zero ₘ ] y ∶ S)

    weaken-∈ : ∀ {Γ} → [ p ] x ∶ T ∈₀ Γ → [ p ] x ∶ T ∈ Γ
    weaken-∈ {Γ = _ ,[ p ] x ∶ T} (here₀ _) = here
    weaken-∈ {Γ = _ ,[ zero ₘ ] x ∶ T} (there₀ ∈₀Γ x≢y) = there (weaken-∈ ∈₀Γ) x≢y 

    ext : (∀ {p x A} → [ p ] x ∶ A ∈ Γ → [ p ] x ∶ A ∈ Δ) →
        ∀ {x y p q A B} → [ p ] x ∶ A ∈ (Γ ,[ q ] y ∶ B) → [ p ] x ∶ A ∈ (Δ ,[ q ] y ∶ B)
    ext μ here = here
    ext μ (there ∈Γ x≢y) = there (μ ∈Γ) x≢y

    ext₀ : (∀ {p x A} → [ p ] x ∶ A ∈₀ Γ → [ p ] x ∶ A ∈₀ Δ) → 
        (∀ {Γ Δ} → 𝟘 Γ ≡ Γ → 𝟘 Δ ≡ Δ) → 
        ∀ {x y p q A B} → [ p ] x ∶ A ∈₀ (Γ ,[ q ] y ∶ B) → [ p ] x ∶ A ∈₀ (Δ ,[ q ] y ∶ B)
    ext₀ μ τ (here₀ 𝟘Γ) = here₀ (τ 𝟘Γ) 
    ext₀ μ τ (there₀ ∈Γ x≢y) = there₀ (μ ∈Γ) x≢y 

    infixl 5 _+_
    _+_ : Context → Context → Context 
    ∅ + ∅ = ∅
    _ + _ = {!   !}

    +-∅-lemmaₗ : Γ₁ + Γ₂ ≡ ∅ → Γ₁ ≡ ∅ 
    +-∅-lemmaₗ = {!   !}

    +-∅-lemmaᵣ :  Γ₁ + Γ₂ ≡ ∅ → Γ₂ ≡ ∅ 
    +-∅-lemmaᵣ = {!   !}

    open import Data.Product
    postulate
        context-split-lemma : [ p ] x ∶ B ∈ Γ → Γ₁ + Γ₂ ≡ Γ → ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ → ∃[ q ] ∃[ r ] ( ([ q ] x ∶ A ∈ Γ₁) × ([ r ] x ∶ A ∈ Γ₂) × (q +ₘ r ≡ p) )




```

```agda
open import Relation.Binary.Definitions

module Substitution (Var : Set) (Quant : Set) (_≟_ : DecidableEquality Var) where
    open Syntax Var Quant

    open import Relation.Nullary using (does) 
    open import Data.Bool using (if_then_else_)

    _[_/_] : Term → Term → Var → Term
    ⋆ [ a / x ] = ⋆
    mult [ a / x ] = mult
    (p +ₘ q) [ a / x ] = (p [ a / x ]) +ₘ (q [ a / x ])
    (p ·ₘ q) [ a / x ] = (p [ a / x ]) ·ₘ (q [ a / x ])
    (q ₘ) [ a / x ] = q ₘ
    (⦅[ p ] y ∶ A ⦆⇒ B) [ a / x ] = 
        if does (x ≟ y) then 
            ⦅[ p [ a / x ] ] y ∶ (A [ a / x ]) ⦆⇒ B 
        else 
            ⦅[ p [ a / x ] ] y ∶ (A [ a / x ]) ⦆⇒ (B [ a / x ])
    (ƛ[ p ] y ∶ A ⇒ B) [ a / x ] = 
        if does (x ≟ y) then 
            ƛ[ p [ a / x ] ] y ∶ (A [ a / x ]) ⇒ B 
        else 
            (ƛ[ p [ a / x ] ] y ∶ (A [ a / x ]) ⇒ (B [ a / x ]))
    (` y) [ a / x ] = if does (x ≟ y) then a else ` y 
    (s ∙ t) [ a / x ] = (s [ a / x ]) ∙ (t [ a / x ])

```

```agda

module Rules (Var : Set) (_≟_ : DecidableEquality Var) (Quant : Set) (IsQuant : IsQuantity Quant) where
    
    open Syntax Var Quant
    open Context Var Quant IsQuant
    open Substitution Var Quant _≟_ 

    private
        variable
            x : Var
            ρ : Quant
            s t a b : Term
            p q r : Term
            A B S T R : Type
            Γ Γ₁ Γ₂ Γ₃ : Context 

    open IsQuantity IsQuant using (_≤_; one; zero)

    data _⊢_∶_ : Context → Term → Type → Set where
        t-var : 
            [ one ₘ ] x ∶ T ∈₀ Γ →
            ----------------------
            Γ ⊢ ` x ∶ T

        t-mult-type :
            Γ ≡ 𝟘 Γ →
            ------------
            Γ ⊢ mult ∶ ⋆

        t-type-type : 
            Γ ≡ 𝟘 Γ →
            ---------
            Γ ⊢ ⋆ ∶ ⋆  

        t-mult-quant :
            --------------
            𝟘 Γ ⊢ ρ ₘ ∶ mult
        
        t-mult-+ :
            Γ₁ ⊢ p ∶ mult →
            Γ₂ ⊢ q ∶ mult →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            (Γ₁ + Γ₂) ≡ Γ →
            -----------------
            Γ ⊢ p +ₘ q ∶ mult

        t-mult-· :
            Γ₁ ⊢ p ∶ mult →
            Γ₂ ⊢ q ∶ mult →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            (Γ₁ + Γ₂) ≡ Γ →
            -----------------
            Γ ⊢ p ·ₘ q ∶ mult 

        t-lam : 
            (Γ₁ ,[ p ] x ∶ A) ⊢ a ∶ B →
            Γ₂ ⊢ p ∶ mult → 
            Γ₃ ⊢ A ∶ ⋆ →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₃ ⌋ →
            -------------------------------------------
            Γ₁ ⊢ (ƛ[ p ] x ∶ A ⇒ a) ∶ (⦅[ p ] x ∶ A ⦆⇒ B)

        t-pi :
            Γ₁ ⊢ p ∶ mult →
            Γ₂ ⊢ A ∶ ⋆ →
            (Γ₃ ,[ p ] x ∶ A) ⊢ B ∶ ⋆ →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₃ ⌋ →
            (Γ₁ + Γ₂ + Γ₃) ≡ Γ → 
            ---------------------------- 
            Γ ⊢ (⦅[ p ] x ∶ A ⦆⇒ B) ∶ ⋆ 
        
        t-app :
            Γ₁ ⊢ s ∶ (⦅[ p ] x ∶ A ⦆⇒ B) →
            Γ₂ ⊢ t ∶ A →
            ⌊ Γ₁ ⌋ ≡ ⌊ Γ₂ ⌋ →
            (Γ₁ + p · Γ₂) ≡ Γ →
            R ≡ (B [ t / x ]) →
            ------------------------------
            Γ ⊢ (s ∙ t) ∶ R 

```


```agda
module Normalization (Var : Set) (_≟_ : DecidableEquality Var) (Quant : Set) (IsQuant : IsQuantity Quant) where

    open Syntax Var Quant
    open Context Var Quant IsQuant
    open Substitution Var Quant _≟_ 
    open Rules Var _≟_ Quant IsQuant 
    
    open import Relation.Nullary
    open import Data.Product

    private
        variable
            x y : Var
            p p′ q q′ r s t u v a b c : Term
            S T A B : Type
            Γ Γ₁ Γ₂ Δ : Context

    module Q = IsQuantity IsQuant
    
    infix 2 _⟶_
    data _⟶_ : Term → Term → Set where 
        β-reduce : ∀ p x A a b → (ƛ[ p ] x ∶ A ⇒ a) ∙ b ⟶ a [ b / x ]
        +-known : ∀ ρ π → ((ρ ₘ) +ₘ (π ₘ)) ⟶ (ρ Q.+ π) ₘ
        ·-known : ∀ ρ π → ((ρ ₘ) ·ₘ (π ₘ)) ⟶ (ρ Q.· π) ₘ
        +-0ₗ : ∀ p → (Q.zero ₘ) +ₘ p ⟶ p  
        +-0ᵣ : ∀ p → p +ₘ (Q.zero ₘ) ⟶ p  
        ·-0ₗ : ∀ p → (Q.zero ₘ) ·ₘ p ⟶ (Q.zero ₘ)  
        ·-0ᵣ : ∀ p → p ·ₘ (Q.zero ₘ) ⟶ (Q.zero ₘ)

    infix 2 _▸_
    data _▸_ : Term → Term → Set where 
        refl-▸ : s ▸ s 
        trans-▸ : a ▸ b → (b⟶c : b ⟶ c) → a ▸ c   

    trans-▸′ : a ▸ b → b ▸ c → a ▸ c
    trans-▸′ a▸b refl-▸ = a▸b 
    trans-▸′ a▸b (trans-▸ b▸c b⟶c) = trans-▸ (trans-▸′ a▸b b▸c) b⟶c

    admissible-subst : [ p ] x ∶ B ∈ Γ → Γ ⊢ a ∶ A → ∅ ⊢ b ∶ B → ∅ ⊢ a [ b / x ] ∶ A
    admissible-subst {a = ⋆} _ (t-type-type _) _ = t-type-type refl
    admissible-subst {a = mult} _ (t-mult-type _) _ = t-mult-type refl
    admissible-subst {a = p +ₘ q} x∈Γ (t-mult-+ ⊢p ⊢q ⌊Γ⌋-≡ Γ-split) ⊢b 
        with (r , s , x∈Γ₁ , x∈Γ₂ , _) ← context-split-lemma x∈Γ Γ-split ⌊Γ⌋-≡ = 
        t-mult-+ (admissible-subst x∈Γ₁ ⊢p ⊢b) (admissible-subst x∈Γ₂ ⊢q ⊢b) refl refl
    admissible-subst {a = p ·ₘ q} x∈Γ (t-mult-· ⊢p ⊢q ⌊Γ⌋-≡ Γ-split) ⊢b 
        with (r , s , x∈Γ₁ , x∈Γ₂ , _) ← context-split-lemma x∈Γ Γ-split ⌊Γ⌋-≡ =
        t-mult-· (admissible-subst x∈Γ₁ ⊢p ⊢b) (admissible-subst x∈Γ₂ ⊢q ⊢b) refl refl 
    admissible-subst {a = ρ ₘ} x∈Γ t-mult-quant ⊢b = t-mult-quant
    admissible-subst {x = x} {a = ⦅[ p ] y ∶ S ⦆⇒ T} x∈Γ (t-pi ⊢p ⊢A ⊢B ⌊Γ⌋₁₂-≡ ⌊Γ⌋₁₃-≡ Γ-split) ⊢b with x ≟ y 
    ... | yes refl = {!   !} -- t-pi {!   !} {!   !} {!   !} {!   !} {!   !}
    ... | no _ = {!   !}
    admissible-subst {a = Syntax.ƛ[ a ] x ∶ x₁ ⇒ a₁} x∈Γ ⊢a ⊢b = {!   !}
    admissible-subst {a = Syntax.` x} x∈Γ ⊢a ⊢b = {!   !}
    admissible-subst {a = a Syntax.∙ a₁} x∈Γ ⊢a ⊢b = {!   !}

```

```agda
module Admissibility (Var : Set) (_≟_ : DecidableEquality Var) (Quant : Set) (IsQuant : IsQuantity Quant) where

    open Syntax Var Quant
    open Context Var Quant IsQuant
    open Substitution Var Quant _≟_ 
    open Rules Var _≟_ Quant IsQuant 

    private
        variable
            x y : Var
            p q r s t : Term
            S T A B : Type
            Γ Δ : Context

    -- rename : 
    --     (∀ {x p A} → [ p ] x ∶ A ∈₀ Γ → [ p ] x ∶ A ∈₀ Δ) →
    --     (∀ {Γ Δ} → 𝟘 Γ ≡ Γ → 𝟘 Δ ≡ Δ) → 
    --     ∀ {t A} → Γ ⊢ t ∶ A → Δ ⊢ t ∶ A
    -- rename μ τ (t-var ∈₀Γ) = t-var (μ ∈₀Γ)
    -- rename {Γ = Γ} {Δ = Δ} μ τ t-mult-type rewrite sym (τ {Γ = 𝟘 Γ} {Δ = Δ} (𝟘-idempotent Γ)) = t-mult-type 
    -- rename μ τ Rules.t-type-type = {!   !}
    -- rename μ τ Rules.t-mult-quant = {!   !}
    -- rename μ τ (Rules.t-mult-+ ⊢t ⊢t₁ x) = {!   !}
    -- rename μ τ (Rules.t-mult-· ⊢t ⊢t₁ x) = {!   !}
    -- rename μ τ (Rules.t-lam ⊢t ⊢t₁ ⊢t₂ x x₁) = {!   !}
    -- rename μ τ (Rules.t-pi ⊢t ⊢t₁ ⊢t₂ x x₁) = {!   !}
    -- rename μ τ (Rules.t-app ⊢t ⊢t₁ x) = {!   !}

```
 
