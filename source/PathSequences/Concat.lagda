--------------------------------------------------------------------------------
Ettore Aldrovandi, ealdrovandi@fsu.edu

November 2022
--------------------------------------------------------------------------------

Port of [HoTT-Agda](https://github.com/HoTT/HoTT-Agda) `PathSeq`
library to TypeTopology.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

module PathSequences.Concat where

open import MLTT.Spartan
open import UF.Base
open import PathSequences.Base

\end{code}

This module handles concatenation of path sequences. The developmenet
is very close to the module `Concat` in the original repository.

\begin{code}

_∙≡_ : {X : 𝓤 ̇} {x y z : X}
     → x ≡ y → y ≡ z → x ≡ z
[] ∙≡ t = t
(p ◃∙ s) ∙≡ t = p ◃∙ (s ∙≡ t)

∙≡-assoc : {X : 𝓤 ̇} {x y z w : X}
         → (s : x ≡ y) (t : y ≡ z) (u : z ≡ w)
         → (s ∙≡ t) ∙≡ u ＝ s ∙≡ (t ∙≡ u)
∙≡-assoc [] t u = refl
∙≡-assoc (p ◃∙ s) t u = ap (p ◃∙_) (∙≡-assoc s t u)

∙≡-assoc-＝ₛ : {X : 𝓤 ̇} {x y z w : X}
            → (s : x ≡ y) (t : y ≡ z) (u : z ≡ w)
            → ((s ∙≡ t) ∙≡ u) ＝ₛ (s ∙≡ (t ∙≡ u))
∙≡-assoc-＝ₛ s t u = ＝ₛ-in (ap (λ v → [ v ↓]) (∙≡-assoc s t u))

[]-∙≡-right-neutral : {X : 𝓤 ̇} {x y : X}
                    → (s : x ≡ y)
                    → s ∙≡ [] ＝ s
[]-∙≡-right-neutral [] = refl
[]-∙≡-right-neutral (p ◃∙ s) = ap (p ◃∙_) ([]-∙≡-right-neutral s)

[]-∙≡-right-neutral-＝ₛ : {X : 𝓤 ̇} {x y : X}
                       → (s : x ≡ y)
                       → s ∙≡ [] ＝ₛ s
[]-∙≡-right-neutral-＝ₛ s = ＝ₛ-in (ap (λ v → [ v ↓]) ([]-∙≡-right-neutral s))

_∙▹_ : {X : 𝓤 ̇} {x y z : X}
     → x ≡ y → y ＝ z → x ≡ z
s ∙▹ p = s ∙≡ (p ◃∎)

≡-to-＝-hom : {X : 𝓤 ̇} {x y z : X}
            → (s : x ≡ y) (t : y ≡ z)
            → ([ s ↓]) ∙ ([ t ↓]) ＝ [ (s ∙≡ t) ↓]
≡-to-＝-hom [] t = refl-left-neutral
≡-to-＝-hom (p ◃∙ s) [] =
              [ (p ◃∙ s) ↓] ∙ [ [] ↓]  ＝⟨ refl-right-neutral [ (p ◃∙ s) ↓] ⁻¹ ⟩
              [ (p ◃∙ s) ↓]            ＝⟨ ap (λ v → [ v ↓]) ([]-∙≡-right-neutral (p ◃∙ s)) ⁻¹ ⟩
              [ (p ◃∙ s ∙≡ []) ↓]       ∎
≡-to-＝-hom (p ◃∙ s) (q ◃∙ t) =
              [ (p ◃∙ s) ↓] ∙ [ (q ◃∙ t) ↓]  ＝⟨ refl ⟩
              (p ∙ [ s ↓]) ∙ [ (q ◃∙ t) ↓]   ＝⟨ ∙assoc p [ s ↓]  [ q ◃∙ t ↓] ⟩
              p ∙ ([ s ↓] ∙ [ q ◃∙ t ↓])     ＝⟨ ap (p ∙_) (≡-to-＝-hom s (q ◃∙ t)) ⟩
              p ∙ [ s ∙≡  (q ◃∙ t) ↓]         ＝⟨ refl ⟩
              [ p ◃∙ s ∙≡ q ◃∙ t ↓]           ∎

[↓]-hom = ≡-to-＝-hom

\end{code}

Tests

\begin{code}

module _ {X : 𝓤 ̇} {x y z t u : X} where
  
  _ : (a : x ＝ y) (b : y ＝ z) (c : z ＝ t) (d : t ＝ u)
    → [ (a ◃∙ b ◃∎ ∙≡ c ◃∙ d ◃∎) ↓] ＝ a ∙ (b ∙ (c ∙ (d ∙ refl)))
  _ = λ a b c d → refl


\end{code}

Fixities

\begin{code}

infixr 80 _∙≡_
infixl 80 _∙▹_

\end{code}
