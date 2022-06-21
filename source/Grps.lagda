\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline --experimental-lossy-unification #-}

open import UF-PropTrunc
open import UF-Quotient

module Grps
        (pt : propositional-truncations-exist)
        (sq : effective-set-quotients-exist)
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

open effective-set-quotients-exist sq

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

\end{code}

\begin{code}

{-
delooping-of-group-isomorphism : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
                               → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                               → is-connected X
                               → is-connected Y
                               → is-groupoid Y
                               → (x₀ : X) (y₀ : Y)
                               → (φ : (x₀ ≡ x₀) → (y₀ ≡ y₀))
                               → is-equiv φ
                               → ((p q : (x₀ ≡ x₀)) → φ (p ∙ q) ≡ φ p ∙ φ q)
                               → X ≃ Y
-}

\end{code}

\begin{code}

≡-fact₁ : {X : 𝓤 ̇  } {x y z : X} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
        → p ∙ q ≡ r
        → q ≡ p ⁻¹ ∙ r
≡-fact₁ refl refl refl refl = refl

≡-fact₁-converse : {X : 𝓤 ̇  } {x y z : X} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
                 → q ≡ p ⁻¹ ∙ r
                 → p ∙ q ≡ r
≡-fact₁-converse p q refl refl = (right-inverse p) ⁻¹

≡-fact₁-bis : {X : 𝓤 ̇  } {x y z : X} (p : x ≡ z) (q : x ≡ y) (r : y ≡ z)
            → p ≡ q ∙ r
            → q ≡ p ∙ r ⁻¹
≡-fact₁-bis p q refl refl = refl

≡-fact₂ : {X : 𝓤 ̇  } {x y : X} (p q : x ≡ y)
        → p ∙ (p ⁻¹ ∙ q) ≡ q
≡-fact₂ p refl = (right-inverse p) ⁻¹

≡-fact₃ : {X : 𝓤 ̇  } {x y z : X} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
        → (q ≡ p ⁻¹ ∙ r)
        → p ∙ q ∙ r ⁻¹ ≡ refl
≡-fact₃ refl q refl refl = refl

≡-fact₄ : {X : 𝓤 ̇  } {x y : X} (p q : x ≡ y)
        → p ⁻¹ ≡ q ⁻¹
        → p ≡ q
≡-fact₄ p q e = p         ≡⟨ (⁻¹-involutive p) ⁻¹ ⟩
                (p ⁻¹) ⁻¹ ≡⟨ ap _⁻¹ e             ⟩
                (q ⁻¹) ⁻¹ ≡⟨ ⁻¹-involutive q      ⟩
                q         ∎

≡-fact₅ : {X : 𝓤 ̇  } {x y : X} (p : x ≡ y) (q : y ≡ x)
        → p ∙ q ≡ refl
        → p ≡ q ⁻¹
≡-fact₅ p refl refl = refl

\end{code}

\begin{code}

≡-refl-equiv : {X : 𝓤 ̇  } {x y : X} (p : x ≡ y) (q : x ≡ y)
             → (refl ≡ p ⁻¹ ∙ q) ≃ (refl ≡ p ∙ q ⁻¹)
≡-refl-equiv p refl = ≃-sym γ
 where
  γ : (refl ≡ p) ≃ (refl ≡ p ⁻¹)
  γ = (ap _⁻¹)
    , (embedding-embedding' _⁻¹ (equivs-are-embeddings _⁻¹ ⁻¹-is-equiv) refl p)

\end{code}

\begin{code}

module setup
        {X : 𝓤 ̇  }
        {Y : 𝓥 ̇  }
        (x₀ : X)
        (y₀ : Y)
        (φ : (x₀ ≡ x₀) → (y₀ ≡ y₀))
        (φ-preserves-refl : φ refl ≡ refl)
        (φ-preserves-∙ : {k l : x₀ ≡ x₀} → φ (k ∙ l) ≡ φ k ∙ φ l)
       where

{-
 φ⁺ : (x₀ ≡ x₀) ≃ (y₀ ≡ y₀)
 φ⁺ = φ , φ-is-equiv

 φ⁻¹ : y₀ ≡ y₀ → x₀ ≡ x₀
 φ⁻¹ = ⌜ φ⁺ ⌝⁻¹

 φ-refl-left-neutral : {l : y₀ ≡ y₀} → φ refl ∙ l ≡ l
 φ-refl-left-neutral {l} =
  φ refl ∙ l         ≡⟨ ap (φ refl ∙_) (e ⁻¹)  ⟩
  φ refl ∙ φ (φ⁻¹ l) ≡⟨ φ-preserves-∙ ⁻¹       ⟩
  φ (refl ∙ φ⁻¹ l)   ≡⟨ ap φ refl-left-neutral ⟩
  φ (φ⁻¹ l)          ≡⟨ e                      ⟩
  l                  ∎
   where
    e : φ (φ⁻¹ l) ≡ l
    e = inverses-are-sections φ φ-is-equiv l

 φ-preserves-refl : φ refl ≡ refl
 φ-preserves-refl = φ refl        ≡⟨ refl ⟩
                    φ refl ∙ refl ≡⟨ φ-refl-left-neutral ⟩
                    refl          ∎
-}

 φ-preserves-refl' : {l : x₀ ≡ x₀} → l ≡ refl → φ l ≡ refl
 φ-preserves-refl' refl = φ-preserves-refl

 φ-preserves-⁻¹ : {l : x₀ ≡ x₀} → φ (l ⁻¹) ≡ φ l ⁻¹
 φ-preserves-⁻¹ {l} = ≡-fact₅ (φ (l ⁻¹)) (φ l) e
  where
   e = φ (l ⁻¹) ∙ φ l ≡⟨ φ-preserves-∙ ⁻¹      ⟩
       φ (l ⁻¹ ∙ l)   ≡⟨ ap φ (left-inverse l) ⟩
       φ refl         ≡⟨ φ-preserves-refl      ⟩
       refl           ∎

\end{code}

\begin{code}

 based-paths : (x : X) (y : Y) → 𝓤 ⊔ 𝓥 ̇
 based-paths x y = (x ≡ x₀) × (y ≡ y₀)

 module _ {x : X} {y : Y} where

{-
  _≈_ : based-paths x y → based-paths x y → 𝓤 ⊔ 𝓥 ̇
  (p , q) ≈ (p' , q') = ∃ l ꞉ x₀ ≡ x₀ , (p ∙ l ≡ p') × (q ∙ φ l ≡ q')

  ≈-is-prop-valued : is-prop-valued _≈_
  ≈-is-prop-valued _ _ = ∃-is-prop
-}

\end{code}

\begin{code}

  _≈_ : based-paths x y → based-paths x y → 𝓥 ̇
  (p , q) ≈ (p' , q') = ∥ φ (p ⁻¹ ∙ p') ≡ q ⁻¹ ∙ q' ∥

  ≈-is-prop-valued : is-prop-valued _≈_
  ≈-is-prop-valued _ _ = ∥∥-is-prop

{-
  ≈-implies-≈' : {b c : based-paths x y} → b ≈ c → b ≈' c
  ≈-implies-≈' {(p , q)} {(p' , q')} = ∥∥-functor γ
   where
    γ : (Σ l ꞉ x₀ ≡ x₀ , (p ∙ l ≡ p') × (q ∙ φ l ≡ q'))
      → φ (p ⁻¹ ∙ p') ≡ q ⁻¹ ∙ q'
    γ (l , u , v) = ≡-fact₁ q (φ (p ⁻¹ ∙ p')) q' e'
     where
      e : l ≡ p ⁻¹ ∙ p'
      e = ≡-fact₁ p l p' u
      e' = q ∙ φ (p ⁻¹ ∙ p') ≡⟨ ap (λ - → q ∙ φ -) (e ⁻¹) ⟩
           q ∙ φ l           ≡⟨ v ⟩
           q'                ∎

  ≈'-implies-≈ : {b c : based-paths x y} → b ≈' c → b ≈ c
  ≈'-implies-≈ {(p , q)} {(p' , q')} = ∥∥-functor γ
   where
    γ : φ (p ⁻¹ ∙ p') ≡ q ⁻¹ ∙ q'
      → Σ l ꞉ x₀ ≡ x₀ , (p ∙ l ≡ p') × (q ∙ φ l ≡ q')
    γ e = (p ⁻¹ ∙ p') , ≡-fact₂ p p'
                      , ≡-fact₁-converse q (φ (p ⁻¹ ∙ p')) q' e

  ≈-and-≈'-coincide : {b c : based-paths x y} → (b ≈ c) ≃ (b ≈' c)
  ≈-and-≈'-coincide {b} {c} =
   logically-equivalent-props-are-equivalent
    (≈-is-prop-valued b c)
    (≈'-is-prop-valued b c)
    ≈-implies-≈'
    ≈'-implies-≈
-}

  ≈-is-reflexive : reflexive _≈_
  ≈-is-reflexive (refl , refl) = ∣ φ-preserves-refl ∣

  ≈-is-symmetric : symmetric _≈_
  ≈-is-symmetric (p , q) (refl , refl) = ∥∥-functor γ
   where
    γ : φ (p ⁻¹) ≡ q ⁻¹ → φ (refl ∙ p) ≡ refl ∙ q
    γ e = φ (refl ∙ p) ≡⟨ φ-preserves-∙                     ⟩
          φ refl ∙ φ p ≡⟨ ap (_∙ φ p) φ-preserves-refl      ⟩
          refl ∙ φ p   ≡⟨ ap (refl ∙_) (≡-fact₄ (φ p) q e') ⟩
          refl ∙ q     ∎
     where
      e' : φ p ⁻¹ ≡ q ⁻¹
      e' = φ-preserves-⁻¹ ⁻¹ ∙ e

  ≈-is-transitive : transitive _≈_
  ≈-is-transitive (p , q) (p' , q') (refl , refl) = ∥∥-functor₂ γ
   where
    γ : φ (p ⁻¹ ∙ p') ≡ q ⁻¹ ∙ q'
      → φ (p' ⁻¹) ≡ q' ⁻¹
      → φ (p ⁻¹) ≡ q ⁻¹
    γ u v = e ⁻¹
     where
      e = q ⁻¹                      ≡⟨ ≡-fact₁-bis (φ (p ⁻¹ ∙ p')) (q ⁻¹) q' u ⟩
          φ (p ⁻¹ ∙ p') ∙ q' ⁻¹     ≡⟨ ap (φ (p ⁻¹ ∙ p') ∙_) (v ⁻¹)            ⟩
          φ (p ⁻¹ ∙ p') ∙ φ (p' ⁻¹) ≡⟨ φ-preserves-∙ ⁻¹                        ⟩
          φ ((p ⁻¹ ∙ p') ∙ p' ⁻¹)   ≡⟨ ap φ (∙assoc (p ⁻¹) p' (p' ⁻¹))         ⟩
          φ (p ⁻¹ ∙ (p' ∙ p' ⁻¹))   ≡⟨ ap (λ - → φ (p ⁻¹ ∙ -)) ((right-inverse p') ⁻¹) ⟩
          φ (p ⁻¹)                  ∎


\end{code}

\begin{code}

  ≈-is-equiv-relation : is-equiv-relation _≈_
  ≈-is-equiv-relation = ≈-is-prop-valued
                      , ≈-is-reflexive
                      , ≈-is-symmetric
                      , ≈-is-transitive

  ≋ : EqRel (based-paths x y)
  ≋ = _≈_ , ≈-is-equiv-relation

\end{code}

\begin{code}

 ≈₀-normal-form : {y : Y} (p : x₀ ≡ x₀) {q : y ≡ y₀}
                → (p , q) ≈ (refl , (q ∙ φ (p ⁻¹)))
 ≈₀-normal-form p {refl} = ∣ e ∣
  where
   e : φ (p ⁻¹) ≡ refl ∙ (refl ∙ φ (p ⁻¹))
   e = (refl-left-neutral ∙ refl-left-neutral) ⁻¹

\end{code}

\begin{code}

 C : X → 𝓤 ⊔ 𝓥 ̇
 C x = Σ y ꞉ Y , (based-paths x y / ≋)

 C₀-normal-form : {y : Y} {p : x₀ ≡ x₀} {q : y ≡ y₀}
                → (y , η/ ≋ (p , q))
                ≡[ C x₀ ]
                  (y , η/ ≋ (refl , (q ∙ φ (p ⁻¹))))
 C₀-normal-form {y} {p} = to-Σ-≡ (refl , η/-identifies-related-points ≋ (≈₀-normal-form p))

\end{code}

\begin{code}

 ι : singleton-type' y₀ → C x₀
 ι (y , q) = y , (η/ ≋ (refl , q))

 ι₂ : ((y , q) : singleton-type' y₀) → based-paths x₀ y / ≋
 ι₂ (y , q) = pr₂ (ι (y , q))

 ι-is-surjection' : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                  → {y : Y} (q' : based-paths x₀ y / ≋)
                  → ∃ s ꞉ domain ι , ι s ≡ (y , q')
 ι-is-surjection' fe {y} = /-induction ≋ (λ q' → ∃-is-prop) γ
  where
   γ : (b : based-paths x₀ y) → ∃ s ꞉ domain ι , ι s ≡ (y , η/ ≋ b)
   γ (p , q) = ∣ (y , (q ∙ φ (p ⁻¹))) , e ∣
    where
     e : ι (y , (q ∙ φ (p ⁻¹))) ≡ (y , η/ ≋ (p , q))
     e = (C₀-normal-form ⁻¹)

 ι-is-surjection : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) → is-surjection ι
 ι-is-surjection fe (y , q') = ι-is-surjection' fe q'

 ι-fiber-equiv : is-groupoid Y → (s : domain ι) → fiber ι (ι s) ≃ domain ι
 ι-fiber-equiv Y-is-groupoid (y , q) =
  fiber ι (ι (y , q))                              ≃⟨ ≃-refl _   ⟩
  (Σ (y' , q') ꞉ S , ι (y' , q') ≡ ι (y , q))      ≃⟨ I          ⟩
  (Σ (y' , q') ꞉ S , Σ e ꞉ y' ≡ y , T (y' , q') e) ≃⟨ II         ⟩
  (Σ (y' , q') ꞉ S , Σ e ꞉ y' ≡ y , e ≡ q' ∙ q ⁻¹) ≃⟨ III        ⟩
  (Σ (y' , q') ꞉ S , 𝟙 {𝓥})                        ≃⟨ ≃-refl _   ⟩
  S × 𝟙                                            ≃⟨ 𝟙-rneutral ⟩
  S                                                ■
   where
    I   = Σ-cong (λ s → Σ-≡-≃)
    III = Σ-cong (λ (y' , q') →
                    singleton-≃-𝟙 (singleton-types'-are-singletons (q' ∙ q ⁻¹)))
    S : 𝓥 ̇
    S = domain ι
    T : ((y' , q') : S) → y' ≡ y → 𝓤 ⊔ 𝓥 ̇
    T (y' , q') e = transport (λ - → based-paths x₀ - / ≋) e
                              (ι₂ (y' , q')) ≡ (ι₂ (y , q))
    II = Σ-cong (λ s → Σ-cong (λ e → h s e))
     where
      h : ((y' , q') : S) (e : y' ≡ y) → T (y' , q') e ≃ (e ≡ q' ∙ q ⁻¹)
      h (y' , q') refl =
       (η/ ≋ (refl , q') ≡ η/ ≋ (refl , q)) ≃⟨ I'       ⟩
       ((refl , q') ≈ (refl , q))           ≃⟨ ≃-refl _ ⟩
       ∥ φ refl ≡ q' ⁻¹ ∙ q ∥              ≃⟨ III'     ⟩
       (φ refl ≡ q' ⁻¹ ∙ q)                 ≃⟨ IV'      ⟩
       (refl ≡ q' ⁻¹ ∙ q)                   ≃⟨ V'       ⟩
       (refl ≡ q' ∙ q ⁻¹)                   ■
        where
         I'   = ≃-sym (≈-coincides-with-quotient-equality ≋)
         III' = prop-is-equivalent-to-its-truncation (Y-is-groupoid _ _)
         IV'  = ≡-cong-l _ _ φ-preserves-refl
         V'   = ≡-refl-equiv q' q

 ι-is-embedding : is-groupoid Y → is-embedding ι
 ι-is-embedding Y-is-groupoid = embedding-criterion ι γ
  where
   γ : (s : domain ι) → is-prop (fiber ι (ι s))
   γ s = equiv-to-prop ⦅1⦆ ⦅2⦆
    where
     ⦅1⦆ : fiber ι (ι s) ≃ domain ι
     ⦅1⦆ = ι-fiber-equiv Y-is-groupoid s
     ⦅2⦆ : is-prop (domain ι)
     ⦅2⦆ = singletons-are-props (singleton-types'-are-singletons y₀)

 ι-is-equiv : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) → is-groupoid Y → is-equiv ι
 ι-is-equiv fe Y-is-groupoid = surjective-embeddings-are-equivs ι
                            (ι-is-embedding Y-is-groupoid) (ι-is-surjection fe)

\end{code}

\begin{code}

 module _
         (fe : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥))
         (Y-is-groupoid : is-groupoid Y)
        where

  C₀-is-singleton : is-singleton (C x₀)
  C₀-is-singleton = equiv-to-singleton' (ι , ι-is-equiv fe Y-is-groupoid)
                                        (singleton-types'-are-singletons y₀)

\end{code}

\begin{code}

  module _
          (X-is-connected : is-connected X)
         where

   C-is-family-of-singletons : (x : X) → is-singleton (C x)
   C-is-family-of-singletons x = ∥∥-rec (being-singleton-is-prop fe) γ
                                        (X-is-connected x₀ x)
    where
     γ : x₀ ≡ x → is-singleton (C x)
     γ p = transport (λ - → is-singleton (C -)) p C₀-is-singleton

   κ : (x : X) → C x
   κ x = center (C-is-family-of-singletons x)

   f : X → Y
   f x = pr₁ (κ x)

   f-preserves-basepoint : f x₀ ≡ y₀
   f-preserves-basepoint =
    ap pr₁ (singletons-are-props C₀-is-singleton (κ x₀) (ι (y₀ , refl)))
   {-                      f x₀                ≡⟨ refl ⟩
                           pr₁ (κ x₀)          ≡⟨ I    ⟩
                           pr₁ (ι (y₀ , refl)) ≡⟨ refl ⟩
                           y₀                  ∎
    where
     I = ap pr₁ (singletons-are-props C₀-is-singleton (κ x₀) (ι (y₀ , refl))) -}

   𝕏 : pointed-type 𝓤
   𝕏 = X , x₀

   𝕐 : pointed-type 𝓥
   𝕐 = Y , y₀

   𝕗 : pointed-map 𝕏 𝕐
   𝕗 = f , f-preserves-basepoint

   private
    l₀ = f-preserves-basepoint

{-
   key-fact' : pr₂ (κ x₀) ≡ {!!} -- η/ ≋ (refl , l₀)
   key-fact' = ap pr₂ (singletons-are-props {!C₀-is-singleton!} {!!} {!!})

   key-fact : (q : f x₀ ≡ y₀)
            → η/ ≋ (refl , q) ≡ pr₂ (κ x₀)
            → q ≡ l₀
   key-fact q e = {!!}
    where
     foo : ι (f x₀ , q) ≡ (f x₀ , η/ ≋ (refl , q))
     foo = refl
     foo' : ι (f x₀ , q) ≡ κ x₀
     foo' = to-Σ-≡ (refl , e)
     c : C x₀
     c = (f x₀) , η/ ≋ (refl , l₀)
     baz : ι (f x₀ , q) ≡ c
     baz = singletons-are-props C₀-is-singleton (ι (f x₀ , q)) c

   key-lemma : {x x' : X} (e : x ≡ x')
               (p : x ≡ x₀) (p' : x' ≡ x₀) (q : f x ≡ y₀) (q' : f x' ≡ y₀)
             → η/ ≋ (p  , q ) ≡ pr₂ (κ x )
             → η/ ≋ (p' , q') ≡ pr₂ (κ x')
             → ap f e ≡ q ∙ l₀ ⁻¹ ∙ ap f (p ⁻¹ ∙ e ∙ p') ∙ l₀ ∙ q' ⁻¹
   key-lemma e refl refl q q' u v = {!!}
-}

   key-lemma : {x x' : X} (e : x ≡ x')
               (p : x ≡ x₀) (p' : x' ≡ x₀) (q : f x ≡ y₀) (q' : f x' ≡ y₀)
             → η/ ≋ (p  , q ) ≡ pr₂ (κ x )
             → η/ ≋ (p' , q') ≡ pr₂ (κ x')
             → q ⁻¹ ∙ ap f e ∙ q' ≡ φ (p ⁻¹ ∙ e ∙ p')
   key-lemma refl p p' q q' u v = {!!}

   transport-lemma : {y y' : Y} (l : y ≡ y₀) (e : y ≡ y')
                   → transport (λ - → based-paths x₀ - / ≋) e (η/ ≋ (refl , l)) ≡ (η/ ≋ (refl , (e ⁻¹ ∙ l)))
   transport-lemma l refl = {!!}

   key-fact : η/ ≋ (refl , l₀) ≡ pr₂ (κ x₀)
   key-fact = {!!}
    where
     aaa : ι (f x₀ , l₀) ≡ κ x₀
     aaa = singletons-are-props C₀-is-singleton (ι (f x₀ , l₀)) (κ x₀)
     bbb : pr₁ (κ x₀) ≡ pr₁ (ι (y₀ , refl))
     bbb = l₀
     ccc : transport (λ - → based-paths x₀ - / ≋) l₀ (pr₂ (κ x₀))
         ≡ η/ ≋ (refl , refl)
     ccc = pr₂ (from-Σ-≡ (singletons-are-props C₀-is-singleton (κ x₀) (y₀ , η/ ≋ (refl , refl))))
     ddd : η/ ≋ (refl , (l₀ ⁻¹ ∙ {!!})) ≡ η/ ≋ (refl , refl)
     ddd = {!?!}
     lem : (q : f x₀ ≡ y₀) → pr₂ (κ x₀) ≡ η/ ≋ (refl , q)
         → l₀ ≡ q
     lem q e = {!!}

   desired : Ω-functor 𝕗 ∼ φ
   desired l = ∥∥-rec (Y-is-groupoid y₀ y₀) γ
                      (η/-is-surjection ≋ pt (pr₂ (κ x₀)))
    where
     γ : (Σ (p , q) ꞉ based-paths x₀ (f x₀) , η/ ≋ (p , q) ≡ pr₂ (κ x₀))
       → Ω-functor 𝕗 l ≡ φ l
     γ ((p , q) , e) = {!!}
      where
       claim : η/ ≋ (refl , l₀) ≡ pr₂ (κ x₀)
       claim = {!!}
       to-prove : l₀ ⁻¹ ∙ ap f l ∙ l₀ ≡ φ l
       to-prove = l₀ ⁻¹ ∙ ap f l ∙ l₀ ≡⟨ key-lemma l refl refl l₀ l₀ claim claim ⟩
                  φ (refl ∙ l) ≡⟨ ap φ refl-left-neutral ⟩
                  φ l ∎
       {-
       claim : ap f l ≡ l₀ ∙ (q ⁻¹ ∙ ap f p ∙ q) ∙ l₀ ⁻¹
       claim = {!!}
       -}

   {-
    Ω-functor 𝕗 p       ≡⟨ refl ⟩
    l₀ ⁻¹ ∙ ap f p ∙ l₀ ≡⟨ {!!} ⟩
    φ p                 ∎
     where
      l₀ = f-preserves-basepoint -}

{-
   f-is-surjection : is-connected Y → is-surjection f
   f-is-surjection Y-is-connected y =
    ∥∥-functor (λ p → transport (fiber f) p γ) (Y-is-connected y₀ y)
     where
      γ : fiber f y₀
      γ = x₀ , f-preserves-basepoint

   module _
           {x x' : X}
           (pₓ  : x ≡ x₀)
           (pₓ' : x' ≡ x₀)
          where

    E₁ : (x ≡ x') ≃ (x₀ ≡ x₀)
    E₁ = (λ p → pₓ ⁻¹ ∙ p ∙ pₓ')
       , ∘-is-equiv (∙-is-equiv-left (pₓ ⁻¹)) (∙-is-equiv-right pₓ')

   module _
           {x x' : X}
           (qₓ  : f x  ≡ y₀)
           (qₓ' : f x' ≡ y₀)
          where

    E₂ : (y₀ ≡ y₀) ≃ (f x ≡ f x')
    E₂ = (λ q → qₓ ∙ q ∙ qₓ' ⁻¹)
       , ∘-is-equiv (∙-is-equiv-left (qₓ)) (∙-is-equiv-right (qₓ' ⁻¹))

   baz : (x x' : X)
       → ∥ Σ pₓ ꞉   x ≡ x₀ , Σ pₓ' ꞉   x' ≡ x₀
         , Σ qₓ ꞉ f x ≡ y₀ , Σ qₓ' ꞉ f x' ≡ y₀
         , ap f ∼ ⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝ ∥
   baz x x' = ∥∥-rec₂ ∥∥-is-prop γ (η/-is-surjection ≋ pt (pr₂ (κ x )))
                                   (η/-is-surjection ≋ pt (pr₂ (κ x')))
    where
     γ : (Σ b  ꞉ based-paths x  (f x)  , η/ ≋ b  ≡ pr₂ (κ x) )
       → (Σ b' ꞉ based-paths x' (f x') , η/ ≋ b' ≡ pr₂ (κ x'))
       → ∥ Σ pₓ ꞉   x ≡ x₀ , Σ pₓ' ꞉   x' ≡ x₀
         , Σ qₓ ꞉ f x ≡ y₀ , Σ qₓ' ꞉ f x' ≡ y₀
         , ap f ∼ ⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝ ∥
     γ ((pₓ , qₓ) , e) ((pₓ' , qₓ') , e') = ∣ pₓ , pₓ' , qₓ , qₓ' , blah ∣
      where
       blah : (p : x ≡ x') → ap f p ≡ (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) p
       blah refl = ∥∥-rec (Y-is-groupoid (f x) (f x)) bzzz
                          (/-is-effective ≋ (e ∙ e' ⁻¹))
        where
         bzzz : φ (pₓ ⁻¹ ∙ pₓ') ≡ qₓ ⁻¹ ∙ qₓ'
              → ap f refl ≡ (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) refl
         bzzz φ-eq = refl                                     ≡⟨ I    ⟩
                     qₓ ∙ φ (pₓ ⁻¹ ∙ pₓ') ∙ qₓ' ⁻¹            ≡⟨ refl ⟩
                     (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) refl ∎
          where
           I = (≡-fact₃ qₓ (φ (pₓ ⁻¹ ∙ pₓ')) qₓ' φ-eq) ⁻¹
-}
{-
   ap-f-is-equiv : (x x' : X) → is-equiv (ap f {x} {x'})
   ap-f-is-equiv x x' = ∥∥-rec (being-equiv-is-prop' fe₁ fe₂ fe₃ fe₄ (ap f))
                               γ (baz x x')
    where
     fe₁ = lower-funext 𝓤 𝓥 fe
     fe₂ = lower-funext 𝓤 𝓤 fe
     fe₃ = lower-funext 𝓥 𝓥 fe
     fe₄ = lower-funext 𝓤 𝓥 fe
     γ : (Σ pₓ ꞉   x ≡ x₀ , Σ pₓ' ꞉   x' ≡ x₀
        , Σ qₓ ꞉ f x ≡ y₀ , Σ qₓ' ꞉ f x' ≡ y₀
        , ap f ∼ ⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝)
       → is-equiv (ap f)
     γ (pₓ , pₓ' , qₓ , qₓ' , H) =
      equiv-closed-under-∼ (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) (ap f)
                           (∘-is-equiv (⌜⌝-is-equiv (E₁ pₓ pₓ'))
                                       (∘-is-equiv φ-is-equiv
                                                   (⌜⌝-is-equiv (E₂ qₓ qₓ'))))
                           H

   f-is-embedding : is-embedding f
   f-is-embedding = embedding'-embedding f ap-f-is-equiv

   f-is-equiv : is-connected Y → is-equiv f
   f-is-equiv Y-is-connected =
    surjective-embeddings-are-equivs f f-is-embedding
                                       (f-is-surjection Y-is-connected)
-}

\end{code}

Final proof

\begin{code}

{-
delooping-of-group-isomorphism = repeating-the-theorem-statement
 where
  repeating-the-theorem-statement : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
                                  → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
                                  → is-connected X
                                  → is-connected Y
                                  → is-groupoid Y
                                  → (x₀ : X) (y₀ : Y)
                                  → (φ : (x₀ ≡ x₀) → (y₀ ≡ y₀))
                                  → is-equiv φ
                                  → ((p q : (x₀ ≡ x₀)) → φ (p ∙ q) ≡ φ p ∙ φ q)
                                  → X ≃ Y
  repeating-the-theorem-statement
   {𝓤} {𝓥} {X} {Y} fe X-is-connected Y-is-connected
   Y-is-groupoid x₀ y₀ φ φ-is-equiv φ-preserves-∙   = e
    where
     open setup x₀ y₀ φ φ-is-equiv (λ {p} {q} → φ-preserves-∙ p q)
     e : X ≃ Y
     e = f          fe Y-is-groupoid X-is-connected
       , f-is-equiv fe Y-is-groupoid X-is-connected Y-is-connected
-}

\end{code}
