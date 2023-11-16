---
title: 2Monoid
author: Ettore Aldrovandi (ealdrovandi@fsu.edu)
start-date: 2023-11-14
---


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

We have two main choices:

1. Assume the structure is given by (_●_,_✶_,e) as above and use all
   the axioms, except the ones that we have proved are consequences of
   the others. We can call these `W I D E monoidal groupoids.`

2. Assume the structure is given by (_●_,e) and only use the axioms
   for _●_, whereas _✶_ and its axioms are obtained by induction, as
   described in 2Groups.Base. Probably this is more in keeping with
   HoTT. We can call these `T I G H T monoidal groupoids` or simply
   `monoidal groupoids`.


\begin{code}

record wide-monoidal-grpd-axioms (X : 𝓤 ̇)
                                 (_●_ : ⊗-structure X)
                                 (_✶_ : ⊗-structure-Id X _●_)
                                 (e : X) : 𝓤 ̇
                                   where
  field
    is-grpd :        is-groupoid X
    is-assoc :       associative _●_
    has-pentagon :   ⊗-assoc-pentagon X _●_ _✶_ is-assoc
    assoc-comp-id :  ⊗-assoc-compatible-with-＝ X _●_ _✶_ is-assoc
    interchange :    ⊗-structure-interchange X _●_ _✶_
    preserves-refl : ⊗-structure-preserves-id X _●_ _✶_

    unit-left : left-neutral e _●_
    unit-right : right-neutral e _●_

    has-assoc-neutral : ⊗-assoc-neutral X _●_ _✶_ is-assoc e unit-left unit-right
    left-comp-id : left-neutral-compatible-with-＝ X _●_ _✶_ e unit-left unit-right
    right-comp-id : right-neutral-compatible-with-＝ X _●_ _✶_ e unit-left unit-right


record monoidal-grpd-axioms (X : 𝓤 ̇ )
                            (_●_ : ⊗-structure X)
                            (e : X) : 𝓤 ̇
                              where
  private
    _✶_ = ⊗-structure-to-Id₂ X _●_
  field
    is-grpd : is-groupoid X
    is-assoc : associative _●_
    has-pentagon : ⊗-assoc-pentagon X _●_ _✶_ is-assoc

    unit-left : left-neutral e _●_
    unit-right : right-neutral e _●_

    has-assoc-neutral : ⊗-assoc-neutral X _●_ _✶_ is-assoc e unit-left unit-right

\end{code}

From another point of view a "monoidal groupoid structure" on the type
X can be viewed as the the data (_●_ , e) together with the axioms.

\begin{code}

record Wide-Monoidal-grpd-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  field
    _⊗_ : ⊗-structure X
    _⊗₁_ : ⊗-structure-Id X _⊗_
    e : X
    is-monoidal-grpd : wide-monoidal-grpd-axioms X _⊗_ _⊗₁_ e
  open wide-monoidal-grpd-axioms is-monoidal-grpd --public

record Monoidal-grpd-structure (X : 𝓤 ̇) : 𝓤 ̇ where
  field
    _⊗_ : ⊗-structure X
    e : X
    is-monoidal-grpd : monoidal-grpd-axioms X _⊗_ e
  open monoidal-grpd-axioms is-monoidal-grpd --public

\end{code}

The types of monoidal groupoids.

\begin{code}

Wide-Monoidal-Grpd : (𝓤 : Universe) → 𝓤 ⁺ ̇
Wide-Monoidal-Grpd 𝓤 = Σ X ꞉ 𝓤 ̇ , Wide-Monoidal-grpd-structure X

Monoidal-Grpd : (𝓤 : Universe) → 𝓤 ⁺ ̇
Monoidal-Grpd 𝓤 = Σ X ꞉ 𝓤 ̇ , Monoidal-grpd-structure X

\end{code}


