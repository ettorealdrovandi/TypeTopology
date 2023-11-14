--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu

November 2023
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --without-K --safe  --exact-split #-}

open import MLTT.Spartan
--open import UF.Base 
open import UF.Groupoids
open import 2Groups.Base

module 2Groups.2Monoid where
\end{code}

Monoidal Groupoids
==================

Given a type X, we define a monoidal groupoid to consist of an
underlying groupoid equipped with a structure consisting of:

_●_ : X → X → X
_✶_ : ∀ {x x' y y'} → x ＝ x' → y ＝ y' → x ● y ＝ x' ● y'
e : X

satisfying all the independent axioms, including interchange and
preservation of reflexivity.

\begin{code}

record monoidal-grpd-axioms (X : 𝓤 ̇)
                            (_●_ : ⊗-structure X)
                            (_✶_ : ⊗-structure-Id X _●_)
                            (e : X) : 𝓤 ̇
                              where
  field
    is-grpd : is-groupoid X
    is-assoc : associative _●_
    has-pentagon : ⊗-assoc-pentagon X _●_ _✶_ is-assoc
    assoc-comp-id : ⊗-assoc-compatible-with-＝ X _●_ _✶_ is-assoc
    interchange : ⊗-structure-interchange X _●_ _✶_
    preserves-refl : ⊗-structure-preserves-id X _●_ _✶_

    unit-left : left-neutral e _●_
    unit-right : right-neutral e _●_

    has-assoc-neutral : ⊗-assoc-neutral X _●_ _✶_ is-assoc e unit-left unit-right
    left-comp-id : left-neutral-compatible-with-＝ X _●_ _✶_ e unit-left unit-right
    right-comp-id : right-neutral-compatible-with-＝ X _●_ _✶_ e unit-left unit-right

\end{code}


From another point of view a "monoidal groupoid structure" on the type
X can be viewed as the the data (_●_ , e) together with the axioms.

\begin{code}

record Monoidal-grpd-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  field
    _⊗_ : ⊗-structure X
    _⊗₁_ : ⊗-structure-Id X _⊗_
    e : X
    is-monoidal-grpd : monoidal-grpd-axioms X _⊗_ _⊗₁_ e
  open monoidal-grpd-axioms is-monoidal-grpd public

\end{code}


The type of monoidal groupoids.

\begin{code}

Monoidal-Grpd : (𝓤 : Universe) → 𝓤 ⁺ ̇
Monoidal-Grpd 𝓤 = Σ X ꞉ 𝓤 ̇ , Monoidal-grpd-structure X

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


