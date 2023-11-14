--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

Begun on July 2022.
Reworked starting on September 2022.
Substantial modifications on November 2023
--------------------------------------------------------------------------------

Basic facts about 2-groups, or categorical groups, or gr-categories,
in another parlance.  These terms all denote the same thing, namely a
monoidal group-like groupoid.  The terminology is as follows:

1. Categorical Group: abbreviated as Cat-Group

   1. Joyal and Street
   1. Brown, Higgins, Porter
   1. Bullejos, Carrasco, Cegarra, Garzón, del Río, …

1. 2-Group

   1. Baez, Baez-Dolan, etc.

1. Gr-Category (= gr-catégorie)

   1. The french Algebraic Geometry school: Breen, Grothendieck, Sinh

The "group-like" refers to the inverse structure in the sense
specified above, that every term x : X possesses a rigid dual xᵛ.

Thus a categorical group, or 2-group, or gr-category is a type
equipped with a monoidal groupoid structure satisfying group-like
axioms.

The idea is to define monoidal structures first, and then add the
duality structure.

This file contains the definitions and axioms for the structures. The
actual types, monoidal groupoids, group-like groupoids are implemented
in separate modules.

\begin{code}

{-# OPTIONS --without-K --safe  --exact-split #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Groupoids

module 2Groups.Base where

\end{code}

I. The main structure
=====================

The mathematical structure of a 2-Group, or categorical group.

The main structure is of course an operation X → X → X as usual, but
since in categorical algebra the underlying carrier is a category, the
structure also affects morphisms. This means the structure also gives
a binary operation on morphisms, in a compatible way.  The most
important property of the structure on morphisms is functoriality,
which in categorical algebra is a reflection of the fact that the
operation is overall a functor.

In our case, we interpret morphisms as paths. Therefore there should
be a companion structure defined on identity types.  More precisely,
given a specific tensor structure on X, we postulate there exists a
tensor structure on identity types, lifting the one on X, and we
require that the tensor structure on the identity types satisfy:

1. an interchange law with respect to the underlying structure which
corresponds to functoriality with respect to path composition; and
2. preserve refl

\begin{code}

⊗-structure : 𝓤 ̇ → 𝓤 ̇
⊗-structure X = X → X → X

⊗-structure-Id : (X : 𝓤 ̇) → ⊗-structure X → 𝓤 ̇
⊗-structure-Id X _●_ = ∀ {x x' y y'} → x ＝ x' → y ＝ y'
                      → x ● y ＝ x' ● y'

⊗-structure-interchange : (X : 𝓤 ̇) 
                            → (_●_ : ⊗-structure X)
                            → ⊗-structure-Id X _●_ → 𝓤 ̇
⊗-structure-interchange X _●_ _✶_ = {x x' x'' y y' y'' : X}
                                      → (p : x ＝ x') (p' : x' ＝ x'')
                                      → (q : y ＝ y') (q' : y' ＝ y'')
                                      → ((p ✶ q) ∙ (p' ✶ q')) ＝ ((p ∙ p') ✶ (q ∙ q'))

⊗-structure-preserves-id : (X : 𝓤 ̇) (_●_ : ⊗-structure X) (_✶_ : ⊗-structure-Id X _●_) → 𝓤 ̇
⊗-structure-preserves-id X _●_ _✶_ = ∀ {x y} → (𝓻𝓮𝒻𝓵 x) ✶ (𝓻𝓮𝒻𝓵 y) ＝ 𝓻𝓮𝒻𝓵 (x ● y)

\end{code}

The product structure on paths can be expressed in iterated form, that
is, given p : x ＝ x' and q : y ＝ y', the product

p ✶ q : x ⊗ y ＝ x' ⊗ y'

is equal to one of the compositions shown in the following
diagram, where we have inserted appropriate instances of refl:

x ⊗ y  ----→ x' ⊗ y
  |              |
  ↓              ↓
x ⊗ y' ----→ x' ⊗ y'

% https://q.uiver.app/?q=WzAsNCxbMCwwLCJ4XFxvdGltZXMgeSJdLFsyLDAsIngnXFxvdGltZXMgeSJdLFsyLDIsIngnXFxvdGltZXMgeSciXSxbMCwyLCJ4XFxvdGltZXMgeSciXSxbMCwyLCJmIFxcb3RpbWVzIGciLDFdLFswLDEsImZcXG90aW1lcyBpZF95Il0sWzEsMiwiaWRfe3gnfVxcb3RpbWVzIGciLDAseyJvZmZzZXQiOi0xfV0sWzAsMywiaWRfeFxcb3RpbWVzIGciLDJdLFszLDIsImZcXG90aW1lcyBpZF97eSd9IiwyXV0=
\[\begin{tikzcd}
	{x\otimes y} && {x'\otimes y} \\
	\\
	{x\otimes y'} && {x'\otimes y'}
	\arrow["{f \otimes g}"{description}, from=1-1, to=3-3]
	\arrow["{f\otimes id_y}", from=1-1, to=1-3]
	\arrow["{id_{x'}\otimes g}", shift left=1, from=1-3, to=3-3]
	\arrow["{id_x\otimes g}"', from=1-1, to=3-1]
	\arrow["{f\otimes id_{y'}}"', from=3-1, to=3-3]
\end{tikzcd}\]

\begin{code}

module _ (X : 𝓤 ̇)
         (_●_ : ⊗-structure X)
         (_✶_ : ⊗-structure-Id X _●_)
         (𝓘 : ⊗-structure-interchange X _●_ _✶_)
--         (𝓲𝓭 : ⊗-structure-preserves-id X _●_ _✶_)
           where

  ⊗-structure-gray₁ : {x x' y y' : X}
                    → (p : x ＝ x') (q : y ＝ y')
                    → p ✶ q ＝ (p ✶ (𝓻𝓮𝒻𝓵 y)) ∙ ((𝓻𝓮𝒻𝓵 x') ✶ q)
  ⊗-structure-gray₁ {x' = x'} {y} p q = p ✶ q                             ＝⟨ refl ⟩
                                        (p ∙ (𝓻𝓮𝒻𝓵 x')) ✶ q               ＝⟨ ap ((p ∙ 𝓻𝓮𝒻𝓵 x') ✶_) (refl-left-neutral ⁻¹) ⟩
                                        (p ∙ (𝓻𝓮𝒻𝓵 x')) ✶ ((𝓻𝓮𝒻𝓵 y) ∙ q)  ＝⟨  𝓘 p refl refl q ⁻¹ ⟩ 
                                        (p ✶ (𝓻𝓮𝒻𝓵 y)) ∙ ((𝓻𝓮𝒻𝓵 x') ✶ q) ∎

  ⊗-structure-gray₂ : {x x' y y' : X}
                    → (p : x ＝ x') (q : y ＝ y')
                    → p ✶ q ＝ ((𝓻𝓮𝒻𝓵 x) ✶ q) ∙ (p ✶ (𝓻𝓮𝒻𝓵 y'))
  ⊗-structure-gray₂ {x} {y' = y'} p q = p ✶ q                             ＝⟨ refl ⟩
                                        p ✶ (q ∙ (𝓻𝓮𝒻𝓵 y'))               ＝⟨ ap (_✶ (q ∙ 𝓻𝓮𝒻𝓵 y')) (refl-left-neutral ⁻¹) ⟩
                                        ((𝓻𝓮𝒻𝓵 x) ∙ p) ✶ (q ∙ (𝓻𝓮𝒻𝓵 y'))  ＝⟨ 𝓘 refl p q refl ⁻¹ ⟩
                                        ((𝓻𝓮𝒻𝓵 x) ✶ q) ∙ (p ✶ (𝓻𝓮𝒻𝓵 y')) ∎

\end{code}

II. Axioms
==========

1. Pentagon:

((xy)z)t → (x(yz))t → x((yz)t)
    |                    |
    ↓                    ↓
(xy)(zt) -----------→ x(y(zt)) 


2. Compatibility with identity types, that is, naturality of the associativity:

(xy)x -----→ x(yz)
  |           |
  ↓           ↓
(x'y')z' --→ x'(y'z')


\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X) (_✶_ : ⊗-structure-Id X _●_) where

  ⊗-assoc-pentagon : associative _●_ → 𝓤 ̇
  ⊗-assoc-pentagon α = {x y z t : X} →
                       ( ((x ● y) ● z) ● t ＝⟨ (α x y z) ✶ (𝓻𝓮𝒻𝓵 t) ⟩
                         (x ● (y ● z)) ● t ＝⟨ α x (y ● z) t ⟩ 
                         x ● ((y ● z) ● t) ＝⟨ (𝓻𝓮𝒻𝓵 x) ✶ (α y z t) ⟩
                         x ● (y ● (z ● t)) ∎ )
                        ＝
                       ( ((x ● y) ● z) ● t ＝⟨ α (x ● y) z t ⟩
                         (x ● y) ● (z ● t) ＝⟨ α x y (z ● t) ⟩
                         x ● (y ● (z ● t)) ∎ )
  -- ⊗-assoc-pentagon α = {x y z t : X} →
  --                      ((α x y z) ✶ (𝓻𝓮𝒻𝓵 t)) ∙ ((α x (y ● z) t) ∙ ((𝓻𝓮𝒻𝓵 x) ✶ (α y z t)))
  --                      ＝ (α (x ● y) z t) ∙ (α x y (z ● t))

  ⊗-assoc-compatible-with-＝ : associative _●_ → 𝓤 ̇
  ⊗-assoc-compatible-with-＝ α =
    ∀ {x y z x' y' z'}
    → (p : x ＝ x')
    → (q : y ＝ y')
    → (r : z ＝ z')
    → ( (x ● y) ● z   ＝⟨ α x y z ⟩
        x ● (y ● z)   ＝⟨ p ✶ (q ✶ r) ⟩
        x' ● (y' ● z') ∎ )
       ＝
      ( (x ● y) ● z    ＝⟨ (p ✶ q) ✶ r ⟩
        (x' ● y') ● z' ＝⟨ α x' y' z' ⟩
        x' ● (y' ● z') ∎ )

\end{code}

If there is a neutral element e, we require the following axioms.

3. Compatibility with associativity:

   (ex)y ---> e(xy)
     |          |
     |          |
     ↓          ↓ 
     xy ======= xy
     

   (xe)y ---> x(ey)
     |          |
     |          |
     ↓          ↓ 
     xy ======= xy


   (xy)e ---> x(ye)
     |          |
     |          |
     ↓          ↓ 
     xy ======= xy

4. Compatibility with the identity types, which translates the
naturality requirement.

    ex ---> ex'
    |       |
    ↓       ↓
    x ----> x'

    xe ---> x'e
    |       |
    ↓       ↓
    x ----> x'


\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X) (_✶_ : ⊗-structure-Id X _●_) where

  ⊗-assoc-neutral-l : associative _●_
                    → (e : X) → left-neutral e _●_ → right-neutral e _●_
                    → 𝓤 ̇
  ⊗-assoc-neutral-l α e l r = ∀ { x y } →
             ((e ● x) ● y ＝⟨ α e x y ⟩
              e ● (x ● y) ＝⟨ l (x ● y) ⟩
              x ● y       ∎)
              ＝
             ((e ● x) ● y ＝⟨ (l x) ✶ (𝓻𝓮𝒻𝓵 y) ⟩
              x ● y       ∎)

  ⊗-assoc-neutral : associative _●_
                  → (e : X) → left-neutral e _●_ → right-neutral e _●_
                  → 𝓤 ̇
  ⊗-assoc-neutral α e l r = ∀ {x y} →
              ((x ● e) ● y ＝⟨ α x e y ⟩
               x ● (e ● y) ＝⟨ (𝓻𝓮𝒻𝓵 x) ✶ (l y) ⟩
               x ● y       ∎)
               ＝
              ((x ● e) ● y ＝⟨ (r x) ✶ (𝓻𝓮𝒻𝓵 y) ⟩
               x ● y       ∎)

  ⊗-assoc-neutral-r : associative _●_
                    → (e : X) → left-neutral e _●_ → right-neutral e _●_
                    → 𝓤 ̇
  ⊗-assoc-neutral-r α e l r = ∀ {x y} →
                    ((x ● y) ● e ＝⟨ α x y e ⟩
                      x ● (y ● e) ＝⟨ (𝓻𝓮𝒻𝓵 x) ✶ (r y) ⟩
                      x ● y       ∎)
                      ＝
                    ((x ● y) ● e ＝⟨ r (x ● y) ⟩
                      x ● y       ∎)

  left-neutral-compatible-with-＝ : (e : X)
                                  → left-neutral e _●_
                                  → right-neutral e _●_
                                  → 𝓤 ̇
  left-neutral-compatible-with-＝ e l r = ∀ {x x'} → (p : x ＝ x')
                                          → (e ● x  ＝⟨ (𝓻𝓮𝒻𝓵 e) ✶ p ⟩
                                             e ● x' ＝⟨ l x' ⟩
                                             x'     ∎ ) ＝ (l x) ∙ p

  right-neutral-compatible-with-＝ : (e : X)
                                   → left-neutral e _●_
                                   → right-neutral e _●_
                                   → 𝓤 ̇
  right-neutral-compatible-with-＝ e l r = ∀ {x x'} → (p : x ＝ x')
                                           → ( x ● e   ＝⟨ p ✶ (𝓻𝓮𝒻𝓵 e) ⟩ 
                                               x' ● e  ＝⟨ r x' ⟩
                                               x'      ∎ ) ＝ (r x) ∙ p


  left-right-neutral-compatibility : (e : X)
                                   → (l : left-neutral e _●_)
                                   → (r : right-neutral e _●_)
                                   → 𝓤 ̇
  left-right-neutral-compatibility e l r = l e ＝ r e
  
\end{code}


III. Redundant Axioms
===================

It is known that the axioms are not all independent. In particular,
`⊗-assoc-neutral-l`, `⊗-assoc-neutral-r`,
`left-right-neutral-compatibility` follow from the rest. The classical
argument, given below, is in:

1. Joyal, Street: Braided Tensor Categories.
2. Mac Lane: Categories for the Working Mathematician.

The proofs are in the module 2Groups.RedundantAxioms


IV. Preserving refl is a consequence of interchange and induction
=================================================================

⊗-structure-preserves-id is a consequence of interchange law and
induction.

\begin{code}

module _ (X : 𝓤 ̇)
         (_●_ : ⊗-structure X)
         (_✶_ : ⊗-structure-Id X _●_)
         (𝓘   : ⊗-structure-interchange X _●_ _✶_)
           where

  ⊗-structure-has-preserves-id : ⊗-structure-preserves-id X _●_ _✶_
  ⊗-structure-has-preserves-id {x} {y} = (𝓻𝓮𝒻𝓵 x) ✶ (𝓻𝓮𝒻𝓵 y)   ＝⟨ ii ⁻¹ ⟩
                                     𝓻𝓮𝒻𝓵 (x ● y) ∎
                                       where
                                         i : (𝓻𝓮𝒻𝓵 x) ✶ (𝓻𝓮𝒻𝓵 y) ＝ (𝓻𝓮𝒻𝓵 x) ✶ (𝓻𝓮𝒻𝓵 y) ∙ (𝓻𝓮𝒻𝓵 x) ✶ (𝓻𝓮𝒻𝓵 y)
                                         i = ⊗-structure-gray₁ X _●_ _✶_ 𝓘 refl refl

                                         ii : 𝓻𝓮𝒻𝓵 (x ● y) ＝ (𝓻𝓮𝒻𝓵 x) ✶ (𝓻𝓮𝒻𝓵 y)
                                         ii = cancel-left i


           
\end{code}


V. Lifting the structure on the carrier to identity types
=========================================================

The product structure on identity types can be obtained from a given
⊗-structure X → X → X using ap. In fact, this can be done in several
ways, but usign ap₂ is the preferred one, because it simultaneously
lifts to both sides of the ⊗-structure. The lifted structure has
interchange and it preserves refl.

\begin{code}

⊗-structure-to-Id₂ : (X : 𝓤 ̇) (_●_ : ⊗-structure X)
                    → ⊗-structure-Id X _●_
⊗-structure-to-Id₂ X _●_ = ap₂ _●_

⊗-structure-to-Id₂-∙ : {X : 𝓤 ̇} (_●_ : ⊗-structure X)
                     → {x x' x'' y y' y'' : X}
                     → (p : x ＝ x') (p' : x' ＝ x'')
                     → (q : y ＝ y') (q' : y' ＝ y'')
                     → (⊗-structure-to-Id₂ X _●_ p q) ∙ (⊗-structure-to-Id₂ X _●_ p' q')
                       ＝ ⊗-structure-to-Id₂ X _●_ (p ∙ p') (q ∙ q')
⊗-structure-to-Id₂-∙ _●_ p p' q q' = (ap₂-∙ _●_ p p' q q') ⁻¹

⊗-structure-to-Id₂-has-interchange : {X : 𝓤 ̇} (_●_ : ⊗-structure X)
                                   → ⊗-structure-interchange X _●_ (⊗-structure-to-Id₂ X _●_)
⊗-structure-to-Id₂-has-interchange = ⊗-structure-to-Id₂-∙

⊗-structure-to-Id₂-refl : {X : 𝓤 ̇} (_●_ : ⊗-structure X) {x y : X}
                        → ⊗-structure-to-Id₂ X _●_ (𝓻𝓮𝒻𝓵 x) (𝓻𝓮𝒻𝓵 y) ＝ 𝓻𝓮𝒻𝓵 (x ● y)
⊗-structure-to-Id₂-refl _●_ = ap₂-refl-left _●_ refl

⊗-structure-to-Id₂-refl' : {X : 𝓤 ̇} (_●_ : ⊗-structure X) {x y : X}
                        → ⊗-structure-to-Id₂ X _●_ (𝓻𝓮𝒻𝓵 x) (𝓻𝓮𝒻𝓵 y) ＝ 𝓻𝓮𝒻𝓵 (x ● y)
⊗-structure-to-Id₂-refl' _●_ = ap₂-refl-right _●_ refl

⊗-structure-to-Id₂-has-preserves-id : {X : 𝓤 ̇} (_●_ : ⊗-structure X)
                                     → ⊗-structure-preserves-id X _●_ (⊗-structure-to-Id₂ X _●_)
⊗-structure-to-Id₂-has-preserves-id = ⊗-structure-to-Id₂-refl

\end{code}


Variants of the lifts. These encapsulate the idea that the ⊗-structure
at the level of identity paths can be decomposed by inserting identity
maps, as explained by the following diagram.


\begin{code}

⊗-structure-ap-left : {X : 𝓤 ̇ } → (_●_ : ⊗-structure X)
                    → {x y : X} → (p : x ＝ y) → (z : X)
                    → x ● z ＝ y ● z
⊗-structure-ap-left _●_ p z = ap (λ v → v ● z) p


⊗-structure-ap-left-∙ : {X : 𝓤 ̇ } → (_●_ : ⊗-structure X)
                      → {x y z : X} (p : x ＝ y) (q : y ＝ z) (t : X)
                      → (⊗-structure-ap-left _●_ p t) ∙ (⊗-structure-ap-left _●_ q t)
                        ＝ ⊗-structure-ap-left _●_ (p ∙ q) t
⊗-structure-ap-left-∙ _●_ p refl t = refl

⊗-structure-ap-right : {X : 𝓤 ̇} → (_●_ : ⊗-structure X)
                     → (z : X) → {x y : X} → (p : x ＝ y)
                     →  z ● x ＝ z ● y
⊗-structure-ap-right _●_ z p = ap (λ v → z ● v) p

⊗-structure-ap-right-∙ : {X : 𝓤 ̇} → (_●_ : ⊗-structure X)
                       → (t : X) {x y z : X} (p : x ＝ y) (q : y ＝ z)
                       → (⊗-structure-ap-right _●_ t p) ∙ (⊗-structure-ap-right _●_ t q)
                         ＝ ⊗-structure-ap-right _●_ t (p ∙ q)
⊗-structure-ap-right-∙ _●_ t p refl = refl

⊗-structure-to-Id : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                   → ⊗-structure-Id X _●_
⊗-structure-to-Id X _●_ {_} {x'} {y} p q =
                    (⊗-structure-ap-left _●_ p y) ∙ (⊗-structure-ap-right _●_ x' q) 

⊗-structure-to-Id' : (X : 𝓤 ̇) → (_●_ : ⊗-structure X)
                    → ⊗-structure-Id X _●_
⊗-structure-to-Id' X _●_ {x} {x'} {y} {y'} p q =
                   (⊗-structure-ap-right _●_ x q) ∙ (⊗-structure-ap-left _●_ p y')


\end{code}

The lifts are compatible. We do this by first expressing the
compatibility via a type, and then, second, showing that this type is
inhabited.

\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X) where

  ⊗-structure-has-compatible-lifts : 𝓤 ̇
  ⊗-structure-has-compatible-lifts = {x x' y y' : X}
                                    → (p : x ＝ x')
                                    → (q : y ＝ y')
                                    → ⊗-structure-to-Id X _●_ {_} {x'} {y} p q 
                                       ＝ ⊗-structure-to-Id' X _●_ {x} {x'} {y} {y'} p q

  ⊗-structure-lifts-compatible : ⊗-structure-has-compatible-lifts
  ⊗-structure-lifts-compatible {x} {.x} {y} {y'} refl q = 
                               ⊗-structure-to-Id X _●_ refl q        ＝⟨ refl ⟩
                               refl ∙ (⊗-structure-ap-right _●_ x q) ＝⟨ refl-left-neutral ⟩
                               ⊗-structure-ap-right _●_ x q          ＝⟨ refl ⁻¹ ⟩
                               (⊗-structure-ap-right _●_ x q) ∙ refl ＝⟨ refl ⟩
                               ⊗-structure-to-Id' X _●_ refl q ∎

  ⊗-structure-has-compatible-lifts₂ : 𝓤 ̇
  ⊗-structure-has-compatible-lifts₂ = {x x' y y' : X}
                                    → (p : x ＝ x')
                                    → (q : y ＝ y')
                                    → ⊗-structure-to-Id₂ X _●_ p q ＝
                                         ⊗-structure-to-Id X _●_ p q

  ⊗-structure-lifts-compatible₂ : ⊗-structure-has-compatible-lifts₂
  ⊗-structure-lifts-compatible₂ refl refl = refl

\end{code}

The interchange law holds for the lifts we have introduced. For
⊗-structure-to-Id₂ this is immediate and it is just the compatibility
with path composition.

\begin{code}

  ⊗-structure-to-Id-has-interchange : ⊗-structure-interchange X _●_ (⊗-structure-to-Id X _●_)
  ⊗-structure-to-Id-has-interchange {x} {x'} {.x'} {y} {.y} {y''} p refl refl q' =
       ⊗-structure-to-Id X _●_ p refl ∙ ⊗-structure-to-Id X _●_ refl q'         ＝⟨ refl ⟩
       ⊗-structure-to-Id X _●_ p refl ∙ (refl ∙ ⊗-structure-ap-right _●_ x' q') ＝⟨ refl ⟩
       (⊗-structure-ap-left _●_ p y)  ∙ (refl ∙ ⊗-structure-ap-right _●_ x' q') ＝⟨ i ⟩
       (⊗-structure-ap-left _●_ p y)  ∙ (⊗-structure-ap-right _●_ x' q')        ＝⟨ refl ⟩
       ⊗-structure-to-Id X _●_ p  q'                                             ＝⟨ refl ⟩
       ⊗-structure-to-Id X _●_ (p ∙ refl) q'                                     ＝⟨ ii ⟩
       ⊗-structure-to-Id X _●_ (p ∙ refl) (refl ∙ q') ∎
         where
           i = ap (λ v → (⊗-structure-ap-left _●_ p y) ∙ v) (refl-left-neutral {p = ⊗-structure-ap-right _●_ x' q'})
           ii = ap (⊗-structure-to-Id X _●_ (p ∙ refl)) (refl-left-neutral {p = q'}) ⁻¹ 
         
\end{code}

Prove that a lifted structure satisfies parts of the axioms

\begin{code}

module _ (X : 𝓤 ̇) (_●_ : ⊗-structure X)  where

  private
   _✶_ = ⊗-structure-to-Id₂ X _●_

  ⊗-structure-to-Id-assoc-compatible-with-＝ : (α : associative _●_)
                                             → ⊗-assoc-compatible-with-＝ X _●_ _✶_ α
  ⊗-structure-to-Id-assoc-compatible-with-＝ α {x} {y} {z} {.x} {.y} {.z} refl refl refl = 
    α x y z ∙ refl ✶ (refl ✶ refl)
      ＝⟨ ap ((α x y z) ∙_) refl ⟩
    α x y z
      ＝⟨ refl-left-neutral  ⁻¹ ⟩
    refl ∙ (α x y z)
      ＝⟨ refl ⟩
    ((refl ✶ refl) ✶ refl) ∙ α x y z ∎

  ⊗-structure-to-Id-left-neutral-compatible-with-＝ : (e : X)
                                                    → (l : left-neutral e _●_)
                                                    → (r : right-neutral e _●_)
                                                    → left-neutral-compatible-with-＝ X _●_ _✶_ e l r
  ⊗-structure-to-Id-left-neutral-compatible-with-＝ e l r {x} refl = refl ✶ refl ∙ (l x ) ＝⟨ refl-left-neutral ⟩
                                                                     l x                  ∎

  ⊗-structure-to-Id-right-neutral-compatible-with-＝ : (e : X)
                                                     → (l : left-neutral e _●_)
                                                     → (r : right-neutral e _●_)
                                                     → right-neutral-compatible-with-＝ X _●_ _✶_ e l r
  ⊗-structure-to-Id-right-neutral-compatible-with-＝ e l r {x} refl = refl ✶ refl ∙ (r x) ＝⟨ refl-left-neutral ⟩
                                                                      r x                 ∎

\end{code}

VI. Duality
===========

Invertibility of the structure operation (duality, in another
parlance) stipulates that for each object X there are two "duality"
morphisms

ε : x  xᵛ → e
η : e → xᵛ x

corresponding to the usual notion of "inverse" elements, such that the
compositions

x → x e → x (xᵛ x) → (x xᵛ) x → e x → x

xᵛ → e xᵛ → (xᵛ x) xᵛ → xᵛ (x xᵛ) → xᵛ e → xᵛ

are the identity.

\begin{code}

module _ (X : 𝓤 ̇) 
         (_●_ : ⊗-structure X)
         (_✶_ : ⊗-structure-Id X _●_)
         (𝓘 : ⊗-structure-interchange X _●_ _✶_)
         (𝓲𝓭 : ⊗-structure-preserves-id X _●_ _✶_)
           where

  ⊗-inv-structure : (e : X)
                   → left-neutral e _●_
                   → right-neutral e _●_
                   → 𝓤 ̇
  ⊗-inv-structure e l r = (x : X) → Σ xᵛ ꞉ X , (x ● xᵛ ＝ e) × (e ＝ xᵛ ● x)

  ⊗-inv-compatible : associative _●_
                   → (e : X) (l : left-neutral e _●_) (r : right-neutral e _●_)
                   → ⊗-inv-structure e l r
                   → 𝓤 ̇
  ⊗-inv-compatible α e l r inv = (x : X) → (p x ＝ refl) × (q x ＝ refl)
    where
      p : (x : X) → x ＝ x
      p x = x            ＝⟨ (r x) ⁻¹ ⟩
            x ● e        ＝⟨ refl ✶ (pr₂ (pr₂ (inv x))) ⟩
            x ● (xᵛ ● x) ＝⟨ (α _ _ _) ⁻¹ ⟩
            (x ● xᵛ) ● x ＝⟨ (pr₁ (pr₂ (inv x))) ✶ refl ⟩
            e ● x        ＝⟨ l x ⟩
            x ∎
            where
              xᵛ : X
              xᵛ = pr₁ (inv x)
      q : (x : X) → pr₁ (inv x) ＝ pr₁ (inv x)
      q x = xᵛ            ＝⟨ (l xᵛ) ⁻¹ ⟩
            e ● xᵛ        ＝⟨ (pr₂ (pr₂ (inv x))) ✶ refl ⟩
            (xᵛ ● x) ● xᵛ ＝⟨ α _ _ _ ⟩
            xᵛ ● (x ● xᵛ) ＝⟨ refl ✶ (pr₁ (pr₂ (inv x))) ⟩
            xᵛ ● e        ＝⟨ r xᵛ ⟩
            xᵛ ∎
            where
              xᵛ : X
              xᵛ = pr₁ (inv x)
\end{code}





