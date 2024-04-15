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
open import CategoricalAlgebra.Base
open import CategoricalAlgebra.MonoidalGroupoids

module CategoricalAlgebra.CatGroups where
\end{code}


Synonyms: categorical group, 2-group, gr-category, group-like groupoid

A type equipped with a monoidal groupoid structure satisfying
group-like axioms.


\begin{code}

record wide-cat-group-axioms (X : 𝓤 ̇ )
                             (_●_ : ⊗-structure X)
                             (_✶_ : ⊗-structure-Id X _●_)
                             (e : X) : 𝓤 ̇
                               where
  field
    instance
      is-monoidal-grpd : wide-monoidal-grpd-axioms X _●_ _✶_ e
  open wide-monoidal-grpd-axioms is-monoidal-grpd --public
  field
    ⊗-inv : ⊗-inv-structure X _●_ _✶_ e unit-left unit-right
    ⊗-inv-axioms : ⊗-inv-compatible X _●_ _✶_ is-assoc e unit-left unit-right ⊗-inv


record cat-group-axioms (X : 𝓤 ̇ )
                        (_●_ : ⊗-structure X)
                        (e : X) : 𝓤 ̇
                          where
  field
    instance
      is-monoidal-grpd : monoidal-grpd-axioms X _●_ e
  open monoidal-grpd-axioms is-monoidal-grpd public
  field
    ⊗-inv : ⊗-inv-structure X _●_ _✶_ e unit-left unit-right
    ⊗-inv-axioms : ⊗-inv-compatible X _●_ _✶_ is-assoc e unit-left unit-right ⊗-inv


record Wide-Cat-Group-structure (X : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    _⊗_  : ⊗-structure X
    _⊗₁_ : ⊗-structure-Id X _⊗_
    e    : X
    instance
      is-cat-group : wide-cat-group-axioms X _⊗_ _⊗₁_ e

record Cat-Group-structure (X : 𝓤 ̇ ) : 𝓤 ̇ where
  field
    _⊗_ : ⊗-structure X
    e   : X
    instance
      is-cat-group : cat-group-axioms X _⊗_ e


2-Group Cat-Group Gr-Cat : (𝓤 : Universe) → 𝓤 ⁺ ̇
2-Group 𝓤 = Σ X ꞉ 𝓤 ̇ , Cat-Group-structure X
Cat-Group = 2-Group
Gr-Cat = 2-Group

\end{code}

Forgetting the group-like structure gives a monoidal groupoid

\begin{code}

cat-group-structure-is-monoidal-grpd-structure : (X : 𝓤 ̇)
                                             → Cat-Group-structure X
                                             → Monoidal-grpd-structure X
cat-group-structure-is-monoidal-grpd-structure X s =
  record { _⊗_ = s ._⊗_ ;
           e = s .e ;
           is-monoidal-grpd = s .is-cat-group .cat-group-axioms.is-monoidal-grpd }
  where
    open Cat-Group-structure


2-groups-are-monoidal-groupoids : 2-Group 𝓤 → Monoidal-Grpd 𝓤
2-groups-are-monoidal-groupoids (X , s) =
  X , cat-group-structure-is-monoidal-grpd-structure X s

\end{code}
