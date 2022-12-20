module GTTM.Syntax (Var : Set) (Quant : Set) where 

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