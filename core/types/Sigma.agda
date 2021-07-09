{-# OPTIONS --without-K --rewriting #-}

open import core.Base
open import core.Path
open import core.PathOver


module core.types.Sigma where

  module _ {i j} {A : Set i} {B : A → Set j} where
  
    pair= : {a a' : A} (p : a ≡ a') {b : B a} {b' : B a'}
      → (q : b ≡ b' [ B ↓ p ])
      → (a , b) ≡ (a' , b')
    pair= refl q = ap (_ ,_) q 

  module _ {i j} {A : Set i} {B : Set j} where
  
    pair×= : {a a' : A} (p : a ≡ a') {b b' : B} (q : b ≡ b')
      → (a , b) ≡ (a' , b')
    pair×= refl q = pair= refl q 
