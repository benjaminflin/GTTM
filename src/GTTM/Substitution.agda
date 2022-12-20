open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import GTTM.Quantity


module GTTM.Substitution (Var : Set) (_≟_ : DecidableEquality Var) (Quant : Set) (IsQuant : IsQuantity Quant) where
    open import GTTM.Syntax Var Quant
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

    -- _⟦_/_⟧ : Context → Term → Var → Context
    -- ∅ ⟦ a / x ⟧ = ∅
    -- (Γ ,[ p ] y ∶ A) ⟦ a / x ⟧ = {!   !} -- if does (x ≟ y) then Γ ,[ p ] y : A else {!   !}
