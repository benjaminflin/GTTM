module GTTM.Syntax (Quant : Set) where 
    
    open import Data.Nat

    private
        variable
            n n′ : ℕ

    data Term : ℕ → Set 

    Type : ℕ → Set
    Type = Term

    data Term where
        ⋆ : Term n 
        mult : Term n
        _ₘ : Quant → Term n
        _+ₘ_ : Term n → Term n → Term n 
        _·ₘ_ : Term n → Term n → Term n 
        ⦅[_]∶_⦆⇒_ : Term n → Term n → Term (suc n) → Term n
        ƛ[_]∶_⇒_ : Term n → Term n → Term (suc n) → Term n
        `_ : n′ < n → Term n 
        _∙_ : Term n → Term n → Term n
