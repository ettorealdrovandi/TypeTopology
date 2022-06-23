\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

open import UF-PropTrunc
open import UF-Quotient

module Grps
        (pt : propositional-truncations-exist)
       where

open import SpartanMLTT

open import UF-Base hiding (_≈_)
open import UF-Embeddings
open import UF-Equiv
open import UF-Equiv-FunExt
open import UF-EquivalenceExamples
open import UF-FunExt
open import UF-Lower-FunExt
open import UF-ImageAndSurjection
open import UF-Subsingletons hiding (Ω)
open import UF-Subsingletons-FunExt

open ImageAndSurjection pt
open PropositionalTruncation pt

\end{code}

\begin{code}

is-connected : 𝓤 ̇  → 𝓤 ̇
is-connected X = (x y : X) → ∥ x ≡ y ∥

is-groupoid : 𝓤 ̇  → 𝓤 ̇
is-groupoid X = (x y : X) → is-set (x ≡ y)

pointed-type : (𝓤 : Universe) → 𝓤 ⁺ ̇
pointed-type 𝓤 = Σ X ꞉ 𝓤 ̇  , X

⟨_⟩ : pointed-type 𝓤 → 𝓤 ̇
⟨_⟩ = pr₁

basepoint : (X : pointed-type 𝓤) → ⟨ X ⟩
basepoint = pr₂

Ω_ : pointed-type 𝓤 → 𝓤 ̇
Ω (X , x₀) = x₀ ≡ x₀

pointed-map : pointed-type 𝓤 → pointed-type 𝓥 → 𝓤 ⊔ 𝓥 ̇
pointed-map (X , x₀) (Y , y₀) = Σ f ꞉ (X → Y) , f x₀ ≡ y₀

Ω-functor : {X : pointed-type 𝓤} {Y : pointed-type 𝓥}
          → pointed-map X Y → Ω X → Ω Y
Ω-functor (f , p) l = p ⁻¹ ∙ ap f l ∙ p

is-Ω-group-homomorphism : {X : pointed-type 𝓤} {Y : pointed-type 𝓥}
                          (φ : Ω X → Ω Y) → 𝓤 ⊔ 𝓥 ̇
is-Ω-group-homomorphism {𝓤} {𝓥} {(X , x₀)} φ =
 (φ refl ≡ refl) × ({k l : x₀ ≡ x₀} → φ (k ∙ l) ≡ φ k ∙ φ l)

\end{code}

\begin{code}

delooping-group-homomorphism : (X : pointed-type 𝓤) (Y : pointed-type 𝓥)
                             → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                             → is-connected ⟨ X ⟩
                             → is-groupoid ⟨ Y ⟩
                             → (φ : Ω X → Ω Y)
                             → is-Ω-group-homomorphism φ
                             → Σ 𝕗 ꞉ pointed-map X Y , Ω-functor 𝕗 ≡ φ

delooping-group-homomorphism-is-unique : (X : pointed-type 𝓤)
                                         (Y : pointed-type 𝓥)
                                       → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                                       → is-connected ⟨ X ⟩
                                       → is-groupoid ⟨ Y ⟩
                                       → (φ : Ω X → Ω Y)
                                       → is-Ω-group-homomorphism φ
                                       → ∃! 𝕗 ꞉ pointed-map X Y , Ω-functor 𝕗 ≡ φ

private
 module construction
         {X : 𝓤 ̇  }
         {Y : 𝓥 ̇  }
         (fe : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥))
         (x₀ : X)
         (y₀ : Y)
         (φ : (x₀ ≡ x₀) → (y₀ ≡ y₀))
         (φ-preserves-refl : φ refl ≡ refl)
         (φ-preserves-∙ : {k l : x₀ ≡ x₀} → φ (k ∙ l) ≡ φ k ∙ φ l)
        where

  fe' : funext 𝓤 𝓥
  fe' = lower-funext 𝓥 𝓤 fe

  is-related-to-φ : {x : X} {y : Y} → (x ≡ x₀ → y ≡ y₀) → 𝓤 ⊔ 𝓥 ̇
  is-related-to-φ {x} {y} ω =
   ((p : x ≡ x₀) (l : x₀ ≡ x₀) → ω (p ∙ l) ≡  ω p ∙ φ l)

  being-related-to-φ-is-prop : is-groupoid Y
                             → {x : X} {y : Y}
                             → (ω : x ≡ x₀ → y ≡ y₀)
                             → is-prop (is-related-to-φ ω)
  being-related-to-φ-is-prop Y-is-groupoid {x} {y} ω =
   Π-is-prop (lower-funext 𝓥 𝓤₀ fe)
             (λ p → Π-is-prop fe'
                              (λ l → Y-is-groupoid y y₀))

  map-related-to-φ : (x : X) (y : Y) → 𝓤 ⊔ 𝓥 ̇
  map-related-to-φ x y = Σ ω ꞉ (x ≡ x₀ → y ≡ y₀) , is-related-to-φ ω

  C : (x : X) → 𝓤 ⊔ 𝓥 ̇
  C x = Σ y ꞉ Y , map-related-to-φ x y

  module _ (y : Y) where

   σ : map-related-to-φ x₀ y → y ≡ y₀
   σ (ω , ω-eq) = ω refl

   τ : (q : y ≡ y₀) → map-related-to-φ x₀ y
   τ q = ω , ω-eq
    where
     ω : x₀ ≡ x₀ → y ≡ y₀
     ω l = q ∙ φ l
     ω-eq : (p l : x₀ ≡ x₀) → ω (p ∙ l) ≡ ω p ∙ φ l
     ω-eq p l = ω (p ∙ l)       ≡⟨ by-definition ⟩
                q ∙ φ (p ∙ l)   ≡⟨ I             ⟩
                q ∙ (φ p ∙ φ l) ≡⟨ II            ⟩
                (q ∙ φ p) ∙ φ l ≡⟨ by-definition ⟩
                ω p ∙ φ l       ∎
      where
       I  = ap (q ∙_) φ-preserves-∙
       II = (∙assoc q (φ p) (φ l)) ⁻¹

   τ-section-of-σ : σ ∘ τ ∼ id
   τ-section-of-σ q = σ (τ q)                  ≡⟨ by-definition ⟩
                      σ ((λ l → q ∙ φ l) , e)  ≡⟨ by-definition ⟩
                      q ∙ φ refl               ≡⟨ I ⟩
                      q ∙ refl                 ≡⟨ by-definition ⟩
                      q                        ∎
    where
     e = pr₂ (τ q)
     I = ap (q ∙_) φ-preserves-refl

   σ-section-of-τ : is-groupoid Y → τ ∘ σ ∼ id
   σ-section-of-τ Y-is-groupoid (ω , ω-eq) =
    to-subtype-≡ (being-related-to-φ-is-prop Y-is-groupoid) equal-maps
    where
     equal-maps : (λ l → σ (ω , ω-eq) ∙ φ l) ≡ ω
     equal-maps = dfunext fe' ptwise-eq
      where
       ptwise-eq : (λ l → σ (ω , ω-eq) ∙ φ l) ∼ ω
       ptwise-eq l = σ (ω , ω-eq) ∙ φ l ≡⟨ by-definition ⟩
                     ω refl ∙ φ l       ≡⟨ I             ⟩
                     ω (refl ∙ l)       ≡⟨ II            ⟩
                     ω l                ∎
        where
         I  = (ω-eq refl l) ⁻¹
         II = ap ω refl-left-neutral

   σ-is-equiv : is-groupoid Y → is-equiv σ
   σ-is-equiv Y-is-groupoid =
    qinvs-are-equivs σ (τ , σ-section-of-τ Y-is-groupoid , τ-section-of-σ)

  C₀-is-singleton : is-groupoid Y → is-singleton (C x₀)
  C₀-is-singleton Y-is-groupoid =
   equiv-to-singleton e (singleton-types'-are-singletons y₀)
    where
     e : (Σ y ꞉ Y , map-related-to-φ x₀ y) ≃ (Σ y ꞉ Y , y ≡ y₀)
     e = Σ-cong (λ y → (σ y , σ-is-equiv y Y-is-groupoid))

  module construction-with-further-assumptions
          (X-is-connected : is-connected X)
          (Y-is-groupoid : is-groupoid Y)
         where

   Cs-are-singletons : (x : X) → is-singleton (C x)
   Cs-are-singletons x =
    ∥∥-rec (being-singleton-is-prop fe)
           (λ e → transport (λ - → is-singleton (C -)) e c₀)
           (X-is-connected x₀ x)
     where
      c₀ : is-singleton (C x₀)
      c₀ = C₀-is-singleton Y-is-groupoid

   κ : (x : X) → C x
   κ x = center (Cs-are-singletons x)

   f : X → Y
   f x = pr₁ (κ x)

   ω : (x : X) → x ≡ x₀ → f x ≡ y₀
   ω x = pr₁ (pr₂ (κ x))

   ω-eq : (x : X)
        → (p : x ≡ x₀) (l : x₀ ≡ x₀)
        → ω x (p ∙ l) ≡ ω x p ∙ φ l
   ω-eq x = pr₂ (pr₂ (κ x))

   f-preserves-basepoint : f x₀ ≡ y₀
   f-preserves-basepoint = ω x₀ refl

   𝕗 : pointed-map (X , x₀) (Y , y₀)
   𝕗 = f , f-preserves-basepoint

   key-fact-generalized : {x : X} (e : x ≡ x₀) → ap f e ∙ (ω x₀ refl) ≡ ω x e
   key-fact-generalized refl = refl-left-neutral

   key-fact : (l : x₀ ≡ x₀) → ap f l ∙ (ω x₀ refl) ≡ ω x₀ l
   key-fact = key-fact-generalized

   key-lemma : (l : x₀ ≡ x₀) → ap f l ∙ ω x₀ refl ≡ ω x₀ refl ∙ φ l
   key-lemma l = ap f l ∙ ω x₀ refl ≡⟨ key-fact l                       ⟩
                 ω x₀ l             ≡⟨ ap (ω x₀) (refl-left-neutral ⁻¹) ⟩
                 ω x₀ (refl ∙ l)    ≡⟨ ω-eq x₀ refl l                   ⟩
                 ω x₀ refl ∙ φ l    ∎

   Ω-functor-𝕗-is-specified-Ω-group-homomorphism : Ω-functor 𝕗 ≡ φ
   Ω-functor-𝕗-is-specified-Ω-group-homomorphism = dfunext fe' ptwise-eq
    where
     l₀ : f x₀ ≡ y₀
     l₀ = f-preserves-basepoint
     ptwise-eq : (l : x₀ ≡ x₀) → Ω-functor 𝕗 l ≡ φ l
     ptwise-eq l = Ω-functor 𝕗 l                          ≡⟨ by-definition ⟩
                   (l₀ ⁻¹ ∙ ap f l) ∙ l₀                  ≡⟨ I             ⟩
                   l₀ ⁻¹  ∙ (ap f l ∙ l₀)                 ≡⟨ by-definition ⟩
                   (ω x₀ refl) ⁻¹  ∙ (ap f l ∙ ω x₀ refl) ≡⟨ use-key-lemma ⟩
                   (ω x₀ refl) ⁻¹ ∙ (ω x₀ refl ∙ φ l)     ≡⟨ II            ⟩
                   ((ω x₀ refl) ⁻¹ ∙ ω x₀ refl) ∙ φ l     ≡⟨ III           ⟩
                   refl ∙ φ l                             ≡⟨ IV            ⟩
                   φ l                                    ∎
      where
       use-key-lemma = ap ((ω x₀ refl) ⁻¹ ∙_) (key-lemma l)
       -- (I) through (IV) are trivialities
       I   = ∙assoc (l₀ ⁻¹) (ap f l) l₀
       II  = (∙assoc (ω x₀ refl ⁻¹) (ω x₀ refl) (φ l)) ⁻¹
       III = ap (_∙ φ l) (left-inverse (ω x₀ refl))
       IV  = refl-left-neutral

   ≡-lemma : {A : 𝓣 ̇  } {a b : A} (p : a ≡ a) (q : a ≡ b) (r : b ≡ b)
           → q ⁻¹ ∙ p ∙ q ≡ r
           → p ∙ q ≡ q ∙ r
   ≡-lemma p refl r refl = (refl ∙ (refl ∙ p) ≡⟨ refl-left-neutral ⟩
                            refl ∙ p          ≡⟨ refl-left-neutral ⟩
                            p                 ∎) ⁻¹

   delooping-is-unique : (𝕘 : pointed-map (X , x₀) (Y , y₀))
                       → Ω-functor 𝕘 ∼ φ
                       → 𝕗 ≡ 𝕘
   delooping-is-unique 𝕘@(g , k₀) e = 𝕗    ≡⟨ by-definition     ⟩
                                      π κᶠ ≡⟨ ap π κᶠ-equals-κᵍ ⟩
                                      π κᵍ ≡⟨ by-definition     ⟩
                                      𝕘    ∎
    where
     κᶠ : (x : X) → C x
     κᶠ = κ
     κᵍ : (x : X) → C x
     κᵍ x = g x , ωᵍ , ωᵍ-eq
      where
       ωᵍ : x ≡ x₀ → g x ≡ y₀
       ωᵍ refl = k₀
       ωᵍ-fact : (p : x ≡ x₀) → ωᵍ p ≡ ap g p ∙ k₀
       ωᵍ-fact refl = refl-left-neutral ⁻¹

       ωᵍ-eq : is-related-to-φ ωᵍ
       ωᵍ-eq refl l = ωᵍ (refl ∙ l)          ≡⟨ I                   ⟩
                      ωᵍ l                   ≡⟨ use-ωᵍ-fact₁        ⟩
                      ap g l ∙ k₀            ≡⟨ use-assumption-on-𝕘 ⟩
                      k₀ ∙ φ l               ≡⟨ II                  ⟩
                      refl ∙ (k₀ ∙ φ l)      ≡⟨ by-definition       ⟩
                      ap g refl ∙ (k₀ ∙ φ l) ≡⟨ III                 ⟩
                      (ap g refl ∙ k₀) ∙ φ l ≡⟨ use-ωᵍ-fact₂        ⟩
                      ωᵍ refl ∙ φ l          ∎
        where
         use-assumption-on-𝕘 = ≡-lemma (ap g l) k₀ (φ l) (e l)
         use-ωᵍ-fact₁ = ωᵍ-fact l
         use-ωᵍ-fact₂ = ap (_∙ φ l) (ωᵍ-fact refl) ⁻¹
         I   = ap ωᵍ refl-left-neutral
         II  = refl-left-neutral ⁻¹
         III = (∙assoc (ap g refl) k₀ (φ l)) ⁻¹

     κᶠ-equals-κᵍ : κᶠ ≡ κᵍ
     κᶠ-equals-κᵍ = Π-is-prop (lower-funext 𝓥 𝓤₀ fe) Cs-are-props κᶠ κᵍ
      where
       Cs-are-props : (x : X) → is-prop (C x)
       Cs-are-props x = singletons-are-props (Cs-are-singletons x)

     π : ((x : X) → C x) → pointed-map (X , x₀) (Y , y₀)
     π γ = (λ x → pr₁ (γ x)) , pr₁ (pr₂ (γ x₀)) refl


delooping-group-homomorphism (X , x₀) (Y , y₀) fe X-is-connected Y-is-groupoid
                             φ (φ-preserves-refl , φ-preserves-∙) = conclusion
  where
   open construction fe x₀ y₀ φ φ-preserves-refl φ-preserves-∙
   open construction-with-further-assumptions X-is-connected Y-is-groupoid

   conclusion : Σ f ꞉ pointed-map (X , x₀) (Y , y₀) , Ω-functor f ≡ φ
   conclusion = 𝕗 , Ω-functor-𝕗-is-specified-Ω-group-homomorphism


delooping-group-homomorphism-is-unique 𝕏@(X , x₀) 𝕐@(Y , y₀) fe
                                       X-is-connected Y-is-groupoid
                                       φ (φ-preserves-refl , φ-preserves-∙) =
 conclusion
  where
   open construction fe x₀ y₀ φ φ-preserves-refl φ-preserves-∙
   open construction-with-further-assumptions X-is-connected Y-is-groupoid

   conclusion : ∃! 𝕗 ꞉ pointed-map 𝕏 𝕐 , Ω-functor 𝕗 ≡ φ
   conclusion = δ , lemma
    where
     δ : Σ 𝕗 ꞉ pointed-map 𝕏 𝕐 , Ω-functor 𝕗 ≡ φ
     δ = delooping-group-homomorphism 𝕏 𝕐 fe
                                      X-is-connected Y-is-groupoid
                                      φ (φ-preserves-refl , φ-preserves-∙)
     lemma : is-central (Σ 𝕗 ꞉ pointed-map 𝕏 𝕐 , Ω-functor 𝕗 ≡ φ) δ
     lemma (𝕗 , 𝕗-eq) = to-subtype-≡ condition-is-prop
                                     (delooping-is-unique 𝕗 (happly 𝕗-eq))
      where
       condition-is-prop : (𝕘 : pointed-map 𝕏 𝕐) → is-prop (Ω-functor 𝕘 ≡ φ)
       condition-is-prop 𝕘 =
        equiv-to-prop (≃-funext fe' (Ω-functor 𝕘) φ)
                                    (Π-is-prop fe' (λ _ → Y-is-groupoid y₀ y₀))

\end{code}
