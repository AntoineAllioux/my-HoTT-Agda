{-# OPTIONS --without-K --rewriting #-}

open import core.Base
open import core.NType

module core.types.Unit where

  ⊤-is-contr : ∀ {ℓ} → is-contr {ℓ} ⊤
  ⊤-is-contr {ℓ} = tt , λ { tt → refl }
