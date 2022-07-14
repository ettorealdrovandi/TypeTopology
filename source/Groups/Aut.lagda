--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

June 2022
--------------------------------------------------------------------------------

If X is a set, Aut X, defined in UF-Equiv, is a group.

We assume functional extensionality at level 𝓤.

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import MLTT.Spartan
open import UF.Base hiding (_≈_)
open import UF.Subsingletons
open import UF.Equiv
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Subsingletons-FunExt
open import UF.Retracts

open import Groups.Groups renaming (_≅_ to _≣_)
open import Groups.Groups-Supplement

module Groups.Aut where

module _ (fe : funext 𝓤 𝓤) (X : 𝓤 ̇) (i : is-set X) where

  is-set-Aut : is-set (Aut X)
  is-set-Aut = Σ-is-set
                  (Π-is-set fe (λ _ → i))
                  λ f → props-are-sets (being-equiv-is-prop'' fe f)


  group-structure-Aut : Aut X → Aut X → Aut X
  group-structure-Aut f g = g ● f

  private
    _·_ = group-structure-Aut

\end{code}

In the following proof of the group axioms, the associativity proof
reproduces that of ≃-assoc in UF-Equiv-FunExt, instead of calling
≃-assoc directly, because the latter uses FunExt and we use funext 𝓤 𝓤
here.  Similarly for the proof of the inverse, which reproduces those
of ≃-sym-is-linv and ≃-sym-is-rinv.

In both cases the key is to use being-equiv-is-prop'' in place of
being-equiv-is-prop.

\begin{code}
  group-axioms-Aut : group-axioms (Aut X) _·_
  group-axioms-Aut = is-set-Aut , assoc-Aut , e , ln-e , rn-e , φ
    where
      assoc-Aut : associative _·_
      assoc-Aut (f , i) (g , j) (h , k) = to-Σ-＝ (p , q)
        where
          p : (f ∘ g) ∘ h ＝ f ∘ (g ∘ h)
          p = refl

          d e : is-equiv (f ∘ g ∘ h)
          d = ∘-is-equiv k (∘-is-equiv j i)
          e = ∘-is-equiv (∘-is-equiv k j) i

          q : transport is-equiv p d ＝ e
          q = being-equiv-is-prop'' fe (f ∘ g ∘ h) _ _

      e : Aut X
      e = id , id-is-equiv X

      ln-e : left-neutral e _·_
      ln-e = λ f → ≃-refl-left' fe fe fe f

      rn-e : right-neutral e _·_
      rn-e = λ f → ≃-refl-right' fe fe fe f

      φ : (f : Aut X) →
          (Σ f' ꞉ Aut X , (f' · f ＝ e) × (f · f' ＝ e))
      pr₁ (φ f) = ≃-sym f
      pr₁ (pr₂ (φ (∣f∣ , is))) = to-Σ-＝ (p  , being-equiv-is-prop'' fe _ _ _)
        where
          p : inverse ∣f∣ is ∘ ∣f∣ ＝ id
          p = dfunext fe (inverses-are-retractions ∣f∣ is)
      pr₂ (pr₂ (φ (∣f∣ , is))) = to-Σ-＝ (p , being-equiv-is-prop'' fe _ _ _)
        where
          p : ∣f∣ ∘ inverse ∣f∣ is ＝ id
          p = dfunext fe (inverses-are-sections ∣f∣ is)

  Group-structure-Aut : Group-structure (Aut X)
  Group-structure-Aut = _·_ , group-axioms-Aut
\end{code}

If φ is an equivalence between X and Y, then it induces a morphism
from Aut X to Aut Y. 

\begin{code}

𝓐ut : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X ≃ Y) → Aut X → Aut Y
𝓐ut φ = λ f → (≃-sym φ ● f ) ● φ

\end{code}

This morphism is a homomorphism for the group
structures defined above.

\begin{code}

module _ (fe : FunExt)
         (X : 𝓤 ̇) (i : is-set X)
         (Y : 𝓥 ̇) (j : is-set Y)
         (φ : X ≃ Y)  where

   private
     gr-s-X  gr-s-Y : _
     gr-s-X = Group-structure-Aut {𝓤} (fe 𝓤 𝓤) X i
     gr-s-Y = Group-structure-Aut {𝓥} (fe 𝓥 𝓥) Y j

   is-hom-𝓐ut : is-hom (Aut X , gr-s-X) (Aut Y , gr-s-Y) (𝓐ut φ)
   is-hom-𝓐ut {f} {g} = (≃-sym φ ● (g ● f )) ● φ                   ＝⟨  ap (_● φ) (ap (≃-sym φ ●_) p) ⟩
                         (≃-sym φ ● ((g ● φ) ● (≃-sym φ ● f))) ● φ ＝⟨  ap (_● φ) (≃-assoc fe (≃-sym φ) (g ● φ) (≃-sym φ ● f)) ⟩
                         ((≃-sym φ ● (g ● φ)) ● (≃-sym φ ● f)) ● φ ＝⟨  (≃-assoc fe (≃-sym φ ● (g ● φ)) (≃-sym φ ● f) φ) ⁻¹ ⟩
                         (≃-sym φ ● (g ● φ)) ● ((≃-sym φ ● f) ● φ) ＝⟨  ap (_● ((≃-sym φ ● f) ● φ)) (≃-assoc fe (≃-sym φ) g φ) ⟩
                         ((≃-sym φ ● g) ● φ) ● ((≃-sym φ ● f) ● φ) ∎
     where
       p = g ● f                    ＝⟨ ap (_● f) (≃-refl-right fe g) ⁻¹ ⟩
           (g ● ≃-refl X) ● f       ＝⟨ ap (_● f) (ap (g ●_) (≃-sym-right-inverse fe φ) ⁻¹) ⟩
           (g ● (φ ● ≃-sym φ)) ● f  ＝⟨ ap (_● f) (≃-assoc fe g φ (≃-sym φ) ) ⟩
           ((g ● φ) ● ≃-sym φ) ● f  ＝⟨ (≃-assoc fe (g ● φ) (≃-sym φ) f) ⁻¹   ⟩
           (g ● φ) ● (≃-sym φ ● f) ∎ 

\end{code}




