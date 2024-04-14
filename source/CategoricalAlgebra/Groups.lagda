--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu

October 2022
--------------------------------------------------------------------------------

Groups are categorical groups.

The key point in the proof is that the extra axioms, namely the
pentagon and the associativity involving the idenity, are
automatically true since the carrier of a group is a set, hence the
path identifications hold automatically.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe  #-}

module CategoricalAlgebra.Groups where

open import MLTT.Spartan
open import UF.Subsingletons
open import Groups.Type
open import UF.Groupoids
open import CategoricalAlgebra.2Monoid
open import CategoricalAlgebra.2Group


open Cat-Group-structure

Group-structure-is-cat-group : (X : Group 𝓤)
                              → Cat-Group-structure ⟨ X ⟩

_⊗_ (Group-structure-is-cat-group X) = multiplication X
e (Group-structure-is-cat-group X) = unit X
is-cat-group (Group-structure-is-cat-group X) = record { is-monoidal-grpd = record
                                                                             { is-grpd = sets-are-groupoids (groups-are-sets X)
                                                                             ; is-assoc = assoc X
                                                                             ; has-pentagon = groups-are-sets X _ _
                                                                             ; unit-left = Groups.Type.unit-left X
                                                                             ; unit-right = Groups.Type.unit-right X
                                                                             ; has-assoc-neutral = groups-are-sets X _ _
                                                                             } ;
                                                         ⊗-inv = λ x → (inv X x) , ((inv-right X x) , (inv-left X x ⁻¹)) ;
                                                         ⊗-inv-axioms = λ _ → (groups-are-sets X _ _) , (groups-are-sets X _ _ ) }

Group-is-2-Group : Group 𝓤 → 2-Group 𝓤
Group-is-2-Group X = ⟨ X ⟩ , Group-structure-is-cat-group  X

\end{code}

