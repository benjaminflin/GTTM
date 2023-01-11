module GTTM.Syntax (Quant : Set) where 
    
    open import Data.Nat
    open import Relation.Binary.PropositionalEquality

    private
        variable
            n n′ : ℕ

    data Term : Set 

    Type : Set 
    Type = Term

    data Binder : Set where
        ƛ Π : Binder

    data MBinop : Set where
        +ₘ ·ₘ : MBinop

    data Term where
        ⋆ : Term  
        mult : Term 
        _ₘ : Quant → Term 
        _⟪_⟫_ : Term → MBinop → Term → Term 
        _⟦_⟧∶_⇒_ : Binder → Term → Term → Term → Term
        `_ : ℕ → Term 
        _∙_ : Term → Term → Term

