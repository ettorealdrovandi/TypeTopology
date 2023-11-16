---
title: 2Group
author: Ettore Aldrovandi (ealdrovandi@fsu.edu)
start-date: 2023-11-16
---

\begin{code}

{-# OPTIONS --without-K --safe  --exact-split #-}

open import MLTT.Spartan
--open import UF.Base 
open import UF.Groupoids
open import 2Groups.Base
open import 2Groups.2Monoid

module 2Groups.2Group where
\end{code}

A categorical group, or 2-group, or gr-category is a type equipped
with a monoidal groupoid structure satisfying group-like axioms.


record cat-group-axioms (X : 𝓤 ̇)
                        (m : Monoidal-grpd-structure X) : 𝓤 ̇
                          where
  open Monoidal-grpd-structure
  field
    ⊗-inv : ⊗-inv-structure X (m ._⊗_)
            (m .e) (m .unit-left) (m .unit-right)

    ⊗-inv-axioms : ⊗-inv-compatible X (m ._⊗_) (m .is-assoc)
                   (m .e) (m .unit-left) (m .unit-right) ⊗-inv


record Cat-Group-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  open Monoidal-grpd-structure public
  open cat-group-axioms public
  field
    isMonoidalGrpd : Monoidal-grpd-structure X
    isCatGroup : cat-group-axioms X isMonoidalGrpd


2-Group Cat-Group Gr-Cat : (𝓤 : Universe) → 𝓤 ⁺ ̇
2-Group 𝓤 = Σ X ꞉ 𝓤 ̇ , Cat-Group-structure X
Cat-Group = 2-Group
Gr-Cat = 2-Group



Forgetting the group-like structure gives a monoidal groupoid



cat-group-structure-is-monoidal-grpd-structure : (X : 𝓤 ̇)
                                             → Cat-Group-structure X
                                             → Monoidal-grpd-structure X
cat-group-structure-is-monoidal-grpd-structure X s = s .Cat-Group-structure.isMonoidalGrpd

2-groups-are-monoidal-groupoids : 2-Group 𝓤 → Monoidal-Grpd 𝓤
2-groups-are-monoidal-groupoids (X , s) = X , cat-group-structure-is-monoidal-grpd-structure X s


