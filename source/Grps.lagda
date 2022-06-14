\begin{code}

{-# OPTIONS --without-K --exact-split --safe --auto-inline #-}

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
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

open ImageAndSurjection pt
open PropositionalTruncation pt
open effective-set-quotients-exist sq

is-connected : 𝓤 ̇  → 𝓤 ̇
is-connected X = (x y : X) → ∥ x ≡ y ∥

is-groupoid : 𝓤 ̇  → 𝓤 ̇
is-groupoid X = (x y : X) → is-set (x ≡ y)

module construction
        {X : 𝓤 ̇  }
        {Y : 𝓥 ̇  }
        (x₀ : X)
        (y₀ : Y)
        (φ : (x₀ ≡ x₀) → (y₀ ≡ y₀))
        (φ-is-equiv : is-equiv φ)
        (φ-preserves-∙ : {k l : x₀ ≡ x₀} → φ (k ∙ l) ≡ φ k ∙ φ l)
       where

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

 φ-preserves-refl' : {l : x₀ ≡ x₀} → l ≡ refl → φ l ≡ refl
 φ-preserves-refl' refl = φ-preserves-refl


{- ------------------------------------------------------------- -}

 based-paths : (x : X) (y : Y) → 𝓤 ⊔ 𝓥 ̇
 based-paths x y = (x ≡ x₀) × (y ≡ y₀)

 module _ {x : X} {y : Y} where

  _≈_ : based-paths x y → based-paths x y → 𝓤 ⊔ 𝓥 ̇
  (p , q) ≈ (p' , q') = ∃ l ꞉ x₀ ≡ x₀ , (p ∙ l ≡ p') × (q ∙ φ l ≡ q')

{-
  _≈'_ : based-paths x y → based-paths x y → 𝓥 ̇
  (p , q) ≈' (p' , q') = ∥ q ∙ φ (p ⁻¹ ∙ p') ≡ q' ∥
-}

  _≈''_ : based-paths x y → based-paths x y → 𝓥 ̇
  (p , q) ≈'' (p' , q') = ∥ φ (p ⁻¹ ∙ p') ≡ q ⁻¹ ∙ q' ∥

{-
  ≈-implies-≈' : (b c : based-paths x y) → b ≈ c → b ≈' c
  ≈-implies-≈' (p , q) (p' , q') = ∥∥-functor γ
   where
    γ : (Σ l ꞉ x₀ ≡ x₀ , (p ∙ l ≡ p') × (q ∙ φ l ≡ q'))
      → q ∙ φ (p ⁻¹ ∙ p') ≡ q'
    γ (l , refl , refl) = q ∙ φ (p ⁻¹ ∙ (p ∙ l)) ≡⟨ ap (λ - → q ∙ φ -) ((∙assoc (p ⁻¹) p l) ⁻¹) ⟩
                          q ∙ φ ((p ⁻¹ ∙ p) ∙ l) ≡⟨ ap (λ - → q ∙ φ (- ∙ l)) (left-inverse p) ⟩
                          q ∙ φ (refl ∙ l)       ≡⟨ ap (λ - → q ∙ φ -) refl-left-neutral ⟩
                          q ∙ φ l                ∎

  ≈'-implies-≈ : (b c : based-paths x y) → b ≈' c → b ≈ c
  ≈'-implies-≈ (p , q) (p' , q') = ∥∥-functor γ
   where
    γ : q ∙ φ (p ⁻¹ ∙ p') ≡ q'
      → Σ l ꞉ x₀ ≡ x₀ , (p ∙ l ≡ p') × (q ∙ φ l ≡ q')
    γ e = (p ⁻¹ ∙ p') , (p ∙ (p ⁻¹ ∙ p') ≡⟨ (∙assoc p (p ⁻¹) p') ⁻¹ ⟩
                         (p ∙ p ⁻¹) ∙ p' ≡⟨ ap (_∙ p') ((right-inverse p) ⁻¹) ⟩
                         refl ∙ p'       ≡⟨ refl-left-neutral ⟩
                         p'              ∎)
                      , e

  ≈-and-≈'-coincide : {b c : based-paths x y} → (b ≈ c) ≃ (b ≈' c)
  ≈-and-≈'-coincide {b} {c} = logically-equivalent-props-are-equivalent
                               ∃-is-prop ∥∥-is-prop (≈-implies-≈' b c) (≈'-implies-≈ b c)
-}

  ≈-and-≈''-coincide : {b c : based-paths x y} → (b ≈ c) ≃ (b ≈'' c)
  ≈-and-≈''-coincide = {!!}

  ≈-is-prop-valued : is-prop-valued _≈_
  ≈-is-prop-valued _ _ = ∃-is-prop

  ≈-is-reflexive : reflexive _≈_
  ≈-is-reflexive (p , q) = ∣ refl , refl , ap (q ∙_) φ-preserves-refl ∣

  ≈-is-symmetric : symmetric _≈_
  ≈-is-symmetric (p , q) (p' , q') = ∥∥-functor γ
   where
    γ : (Σ l ꞉ x₀ ≡ x₀ , (p  ∙ l ≡ p') × (q  ∙ φ l ≡ q'))
      → (Σ l ꞉ x₀ ≡ x₀ , (p' ∙ l ≡ p ) × (q' ∙ φ l ≡ q))
    γ (l , u , v) = (l ⁻¹) , u' , v'
     where
      e : l ∙ l ⁻¹ ≡ refl
      e = (right-inverse l) ⁻¹
      u' = p' ∙ l ⁻¹        ≡⟨ ap (_∙ l ⁻¹) (u ⁻¹) ⟩
           (p ∙ l) ∙ l ⁻¹   ≡⟨ ∙assoc p l (l ⁻¹)   ⟩
           p ∙ (l ∙ l ⁻¹)   ≡⟨ ap (p ∙_) e         ⟩
           p                ∎
      v' = q' ∙ φ (l ⁻¹)        ≡⟨ ap (_∙ φ (l ⁻¹)) (v ⁻¹)      ⟩
           (q ∙ φ l) ∙ φ (l ⁻¹) ≡⟨ ∙assoc q (φ l) (φ (l ⁻¹))    ⟩
           q ∙ (φ l ∙ φ (l ⁻¹)) ≡⟨ ap (q ∙_) (φ-preserves-∙ ⁻¹) ⟩
           q ∙ φ (l ∙ l ⁻¹)     ≡⟨ ap (λ - → q ∙ φ -) e         ⟩
           q ∙ φ refl           ≡⟨ ap (q ∙_) φ-preserves-refl   ⟩
           q                    ∎

  ≈-is-transitive : transitive _≈_
  ≈-is-transitive (p , q) (p' , q') (p'' , q'') u v = w
   where
    w : (p , q) ≈ (p'' , q'')
    w = ∥∥-functor₂ γ u v
     where
      γ : (Σ k ꞉ x₀ ≡ x₀ , (p  ∙ k ≡ p' ) × (q  ∙ φ k ≡ q' ))
        → (Σ l ꞉ x₀ ≡ x₀ , (p' ∙ l ≡ p'') × (q' ∙ φ l ≡ q''))
        → (Σ m ꞉ x₀ ≡ x₀ , (p  ∙ m ≡ p'') × (q  ∙ φ m ≡ q''))
      γ (k , a₁ , a₂) (l , b₁ , b₂) = (k ∙ l) , c₁ , c₂
       where
        c₁ = p ∙ (k ∙ l) ≡⟨ (∙assoc p k l) ⁻¹ ⟩
             (p ∙ k) ∙ l ≡⟨ ap (_∙ l) a₁      ⟩
             p' ∙ l      ≡⟨ b₁                ⟩
             p''         ∎
        c₂ = q ∙ φ (k ∙ l)   ≡⟨ ap (q ∙_) φ-preserves-∙   ⟩
             q ∙ (φ k ∙ φ l) ≡⟨ (∙assoc q (φ k) (φ l)) ⁻¹ ⟩
             (q ∙ φ k) ∙ φ l ≡⟨ ap (_∙ φ l) a₂            ⟩
             q' ∙ φ l        ≡⟨ b₂                        ⟩
             q'' ∎

  ≈-is-equiv-relation : is-equiv-relation _≈_
  ≈-is-equiv-relation = ≈-is-prop-valued
                      , ≈-is-reflexive
                      , ≈-is-symmetric
                      , ≈-is-transitive

  ≋ : EqRel (based-paths x y)
  ≋ = _≈_ , ≈-is-equiv-relation

{- --------------------------------------------------------------------------- -}

 ≈₀-normal-form : {y : Y} {p : x₀ ≡ x₀} {q : y ≡ y₀}
                → (p , q) ≈ (refl , (q ∙ φ (p ⁻¹)))
 ≈₀-normal-form {y} {p} {q} = ∣ (p ⁻¹) , ((right-inverse p) ⁻¹) , refl ∣

{-
 ≈₀-transport-lemma : {x : X} {y y' : Y} (e : y ≡ y') (q : y ≡ y₀)
                   → transport (λ - → based-paths x₀ - / ≋) e (η/ ≋ (refl , q))
                   ≡ η/ ≋ (refl , (e ⁻¹ ∙ q))
 ≈₀-transport-lemma refl q = ap (λ - → η/ ≋ (refl , -)) lem
  where
   lem = q           ≡⟨ refl-left-neutral ⁻¹ ⟩
         refl ∙ q    ≡⟨ refl ⟩
         refl ⁻¹ ∙ q ∎

 ≈₀-eq-lemma : {y y' : Y} (e : y ≡ y') (q : y ≡ y₀) (q' : y' ≡ y₀)
             → (refl , (e ⁻¹ ∙ q)) ≈ (refl , q')
             ≃ ∥ e ≡ q ∙ q' ⁻¹ ∥
 ≈₀-eq-lemma e q q' =
  (refl , (e ⁻¹ ∙ q)) ≈ (refl , q') ≃⟨ ≈-and-≈'-coincide ⟩
  ∥ e ⁻¹ ∙ q ∙ φ refl ≡ q' ∥        ≃⟨ γ e q q' ⟩
  ∥ e ≡ q ∙ q' ⁻¹ ∥                 ■
   where
    γ : {y y' : Y} (e : y ≡ y') (q : y ≡ y₀) (q' : y' ≡ y₀)
      → ∥ e ⁻¹ ∙ q ∙ φ refl ≡ q' ∥ ≃ ∥ e ≡ q ∙ q' ⁻¹ ∥
    γ e refl refl = logically-equivalent-props-are-equivalent ∥∥-is-prop ∥∥-is-prop
                     (∥∥-functor f) (∥∥-functor g)
     where
      f : e ⁻¹ ∙ φ refl ≡ refl → e ≡ refl
      f p = e         ≡⟨ (⁻¹-involutive e) ⁻¹ ⟩
            (e ⁻¹) ⁻¹ ≡⟨ ap _⁻¹ I ⟩
            refl ⁻¹   ≡⟨ refl ⟩
            refl      ∎
       where
        I = e ⁻¹          ≡⟨ refl ⟩
            e ⁻¹ ∙ refl   ≡⟨ II   ⟩
            e ⁻¹ ∙ φ refl ≡⟨ p    ⟩
            refl          ∎
         where
          II = ap (e ⁻¹ ∙_) (φ-preserves-refl ⁻¹)
      g : e ≡ refl → e ⁻¹ ∙ φ refl ≡ refl
      g refl = refl ⁻¹ ∙ φ refl ≡⟨ refl              ⟩
               refl ∙ φ refl    ≡⟨ refl-left-neutral ⟩
               φ refl           ≡⟨ φ-preserves-refl  ⟩
               refl             ∎

 ≈₀-η/-eq-lemma : {y y' : Y} (e : y ≡ y') (q : y ≡ y₀) (q' : y' ≡ y₀)
                → (η/ ≋ (refl , (e ⁻¹ ∙ q)) ≡ η/ ≋ (refl , q'))
                ≃ ∥ e ≡ q ∙ q' ⁻¹ ∥
 ≈₀-η/-eq-lemma e q q' =
  (η/ ≋ (refl , (e ⁻¹ ∙ q)) ≡ η/ ≋ (refl , q')) ≃⟨ γ                  ⟩
  ((refl , (e ⁻¹ ∙ q)) ≈ (refl , q'))           ≃⟨ ≈₀-eq-lemma e q q' ⟩
  ∥ e ≡ q ∙ q' ⁻¹ ∥                             ■
   where
    γ = logically-equivalent-props-are-equivalent
         (/-is-set ≋)
         (≈-is-prop-valued _ _)
         (/-is-effective ≋) -- NB: We use that the quotient is effective here
         (η/-identifies-related-points ≋)
-}

{- --------------------------------------------------------------------------- -}

 module _ (x : X) where

  C : 𝓤 ⊔ 𝓥 ̇
  C = Σ y ꞉ Y , (based-paths x y / ≋)

 C₀-normal-form : {y : Y} {p : x₀ ≡ x₀} {q : y ≡ y₀}
                → (y , η/ ≋ (p , q))
                ≡[ C x₀ ]
                  (y , η/ ≋ (refl , (q ∙ φ (p ⁻¹))))
 C₀-normal-form = to-Σ-≡ (refl , η/-identifies-related-points ≋ ≈₀-normal-form)

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

{-
 foo : {A : 𝓣 ̇  } {a : A} (p : a ≡ a)
     → (refl ≡ p) ≃ (refl ≡ p ⁻¹)
 foo p = qinveq f (g , {!!})
  where
   f : refl ≡ p → refl ≡ p ⁻¹
   f refl = refl
   g : refl ≡ p ⁻¹ → refl ≡ p
   g e = refl ≡⟨ refl ⟩
         refl ⁻¹ ≡⟨ ap _⁻¹ {!!} ⟩
         (p ⁻¹)⁻¹ ≡⟨ {!!} ⟩
         p ∎ -}

 foo : {A : 𝓣 ̇  } {a b : A} (p : a ≡ b) (q : a ≡ b)
     → (refl ≡ p ⁻¹ ∙ q) ≃ (refl ≡ p ∙ q ⁻¹)
 foo p refl = ≃-sym γ
  where
   γ : (refl ≡ p) ≃ (refl ≡ p ⁻¹)
   γ = (ap _⁻¹)
     , (embedding-embedding' _⁻¹ (equivs-are-embeddings _⁻¹ ⁻¹-is-equiv) refl p)

 foo2 : {A : 𝓣 ̇  } {a b c : A} (p : a ≡ c) (q : b ≡ a) (r : b ≡ c)
      → (p ≡ q ⁻¹ ∙ r) → q ∙ p ∙ r ⁻¹ ≡ refl
 foo2 p refl refl refl = refl

 ι-is-embedding : is-groupoid Y → is-embedding ι
 ι-is-embedding Y-grpd = embedding-criterion ι γ
  where
   γ : (s : singleton-type' y₀) → is-prop (fiber ι (ι s))
   γ (y , q) = equiv-to-prop ⦅1⦆ ⦅2⦆
    where
     S : 𝓥 ̇
     S = singleton-type' y₀
     ⦅2⦆ : is-prop S
     ⦅2⦆ = singletons-are-props (singleton-types'-are-singletons y₀)
     T : ((y' , q') : S) (e : y' ≡ y) → 𝓤 ⊔ 𝓥 ̇
     T (y' , q') e =
      transport (λ - → based-paths x₀ - / ≋) e (ι₂ (y' , q')) ≡ (ι₂ (y , q))
     h : ((y' , q') : S) (e : y' ≡ y)
       → T (y' , q') e ≃ (e ≡ q' ∙ q ⁻¹)
     h (y' , q') refl =
      (η/ ≋ (refl , q') ≡ η/ ≋ (refl , q)) ≃⟨ ≃-sym (≈-coincides-with-quotient-equality ≋) ⟩
      ((refl , q') ≈ (refl , q))           ≃⟨ ≈-and-≈''-coincide ⟩
      ((refl , q') ≈'' (refl , q))         ≃⟨ ≃-refl _ ⟩
      ∥ φ refl ≡ q' ⁻¹ ∙ q ∥               ≃⟨ prop-is-equivalent-to-its-truncation (Y-grpd _ _) ⟩
      (φ refl ≡ q' ⁻¹ ∙ q)                 ≃⟨ ≡-cong-l _ _ φ-preserves-refl ⟩
      (refl ≡ q' ⁻¹ ∙ q)                   ≃⟨ foo q' q ⟩
      (refl ≡ q' ∙ q ⁻¹)                   ■
     ⦅1⦆ = fiber ι (ι (y , q))                             ≃⟨ ≃-refl _ ⟩
          (Σ (y' , q') ꞉ S , ι (y' , q') ≡ ι (y , q))      ≃⟨ Σ-cong (λ s → Σ-≡-≃) ⟩
          (Σ (y' , q') ꞉ S , Σ e ꞉ y' ≡ y , T (y' , q') e) ≃⟨ Σ-cong (λ s → Σ-cong (λ e → h s e)) ⟩
          (Σ (y' , q') ꞉ S , Σ e ꞉ y' ≡ y , e ≡ q' ∙ q ⁻¹) ≃⟨ Σ-cong (λ (y' , q') → singleton-≃-𝟙 (singleton-types'-are-singletons (q' ∙ q ⁻¹))) ⟩
          (Σ (y' , q') ꞉ S , 𝟙 {𝓥})                        ≃⟨ ≃-refl _ ⟩
          S × 𝟙                                            ≃⟨ 𝟙-rneutral ⟩
          S                                                ■

 ι-is-equiv : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥) → is-groupoid Y → is-equiv ι
 ι-is-equiv fe Y-grpd = surjective-embeddings-are-equivs ι
                               (ι-is-embedding Y-grpd) (ι-is-surjection fe)

 module _
         (fe : funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥))
         (Y-grpd : is-groupoid Y)
        where

  C₀-is-singleton : is-singleton (C x₀)
  C₀-is-singleton = equiv-to-singleton' (ι , ι-is-equiv fe Y-grpd)
                                        (singleton-types'-are-singletons y₀)

  module _
          (X-con : is-connected X)
         where

   C-is-family-of-singletons : (x : X) → is-singleton (C x)
   C-is-family-of-singletons x = ∥∥-rec (being-singleton-is-prop fe) γ
                                        (X-con x₀ x)
    where
     γ : x₀ ≡ x → is-singleton (C x)
     γ p = transport (λ - → is-singleton (C -)) p C₀-is-singleton

   κ : (x : X) → C x
   κ x = center (C-is-family-of-singletons x)

   f : X → Y
   f x = pr₁ (κ x)

   f-preserves-basepoint : f x₀ ≡ y₀
   f-preserves-basepoint = f x₀                ≡⟨ refl ⟩
                           pr₁ (κ x₀)          ≡⟨ I ⟩
                           pr₁ (ι (y₀ , refl)) ≡⟨ refl ⟩
                           y₀                  ∎
    where
     I = ap pr₁ (singletons-are-props C₀-is-singleton (κ x₀) (ι (y₀ , refl)))

   f-is-surjection : is-connected Y → is-surjection f
   f-is-surjection Y-con y =
    ∥∥-functor (λ p → transport (fiber f) p γ) (Y-con y₀ y)
     where
      γ : fiber f y₀
      γ = x₀ , f-preserves-basepoint

   -- TODO: Move
   η/-is-surjection : {x : X} {y : Y} → is-surjection (η/ (≋ {x} {y}))
   η/-is-surjection = /-induction ≋ (λ _ → ∃-is-prop) (λ b → ∣ b , refl ∣)

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
   baz x x' = ∥∥-rec₂ ∥∥-is-prop γ (η/-is-surjection (pr₂ (κ x))) (η/-is-surjection (pr₂ (κ x'))) -- TODO: Clean
    where
     T : 𝓤 ⊔ 𝓥 ̇
     T = Σ pₓ ꞉   x ≡ x₀ , Σ pₓ' ꞉   x' ≡ x₀
       , Σ qₓ ꞉ f x ≡ y₀ , Σ qₓ' ꞉ f x' ≡ y₀
       , ap f ∼ ⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝
     γ : (Σ b  ꞉ based-paths x  (f x)  , η/ ≋ b  ≡ pr₂ (κ x) )
       → (Σ b' ꞉ based-paths x' (f x') , η/ ≋ b' ≡ pr₂ (κ x'))
       → ∥ T ∥
     γ ((pₓ , qₓ) , e) ((pₓ' , qₓ') , e') = ∣ pₓ , pₓ' , qₓ , qₓ' , blah ∣
      where
       blah : (p : x ≡ x') → ap f p ≡ (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) p
       blah refl = ∥∥-rec (Y-grpd (f x) (f x)) minor (/-is-effective ≋ (e ∙ e' ⁻¹))
        where
         minor : (Σ l ꞉ x₀ ≡ x₀ , (pₓ ∙ l ≡ pₓ') × (qₓ ∙ φ l ≡ qₓ')) -- TODO: Use ≈'' and foo2 here
               → ap f refl ≡ (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) refl
         minor (l , u , v) =
          ap f refl ≡⟨ refl ⟩
          refl ≡⟨ right-inverse qₓ' ⟩
          qₓ' ∙ qₓ' ⁻¹ ≡⟨ ap (_∙ qₓ' ⁻¹) (v ⁻¹) ⟩
          qₓ ∙ φ l ∙ qₓ' ⁻¹ ≡⟨ ap (λ - → qₓ ∙ φ - ∙ qₓ' ⁻¹) kkk ⟩
          qₓ ∙ φ (pₓ ⁻¹ ∙ pₓ') ∙ qₓ' ⁻¹            ≡⟨ refl ⟩
          (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) refl ∎
          where
           kkk : l ≡ pₓ ⁻¹ ∙ pₓ'
           kkk = l                ≡⟨ refl-left-neutral ⁻¹ ⟩
                 refl ∙ l         ≡⟨ ap (_∙ l) ((left-inverse pₓ) ⁻¹) ⟩
                 (pₓ ⁻¹ ∙ pₓ) ∙ l ≡⟨ ∙assoc (pₓ ⁻¹) pₓ l ⟩
                 pₓ ⁻¹ ∙ (pₓ ∙ l) ≡⟨ ap (pₓ ⁻¹ ∙_) u ⟩
                 pₓ ⁻¹ ∙ pₓ'      ∎

   ap-f-is-equiv : (x x' : X) → is-equiv (ap f {x} {x'})
   ap-f-is-equiv x x' = ∥∥-rec (being-equiv-is-prop' fe₁ fe₂ fe₃ fe₄ (ap f))
                               γ (baz x x')
    where
     fe₁ : funext 𝓥 𝓤
     fe₁ = lower-funext 𝓤 𝓥 fe
     fe₂ : funext 𝓥 𝓥
     fe₂ = lower-funext 𝓤 𝓤 fe
     fe₃ : funext 𝓤 𝓤
     fe₃ = lower-funext 𝓥 𝓥 fe
     fe₄ : funext 𝓥 𝓤
     fe₄ = lower-funext 𝓤 𝓥 fe
     γ : (Σ pₓ ꞉   x ≡ x₀ , Σ pₓ' ꞉   x' ≡ x₀
        , Σ qₓ ꞉ f x ≡ y₀ , Σ qₓ' ꞉ f x' ≡ y₀
        , ap f ∼ ⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝)
       → is-equiv (ap f)
     γ (pₓ , pₓ' , qₓ , qₓ' , H) =
      equiv-closed-under-∼ (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) (ap f)
                           (∘-is-equiv (⌜⌝-is-equiv (E₁ pₓ pₓ'))
                                       (∘-is-equiv φ-is-equiv (⌜⌝-is-equiv (E₂ qₓ qₓ'))))
                           H

   f-is-embedding : is-embedding f
   f-is-embedding = embedding'-embedding f ap-f-is-equiv

   f-is-equiv : is-connected Y → is-equiv f
   f-is-equiv Y-con = surjective-embeddings-are-equivs f f-is-embedding (f-is-surjection Y-con)

-- Repackaging

theorem : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
        → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
        → is-connected X
        → is-connected Y
        → is-groupoid Y
        → (x₀ : X) (y₀ : Y)
        → (φ : (x₀ ≡ x₀) ≃ (y₀ ≡ y₀))
        → ((p q : (x₀ ≡ x₀)) → ⌜ φ ⌝ (p ∙ q) ≡ ⌜ φ ⌝ p ∙ ⌜ φ ⌝ q)
        → X ≃ Y
theorem fe X-con Y-con Y-grpd x₀ y₀ (φ , φ-is-equiv) φ-preserves-∙ =
   f          fe Y-grpd X-con
 , f-is-equiv fe Y-grpd X-con Y-con
  where
   open construction x₀ y₀ φ φ-is-equiv (λ {p} {q} → φ-preserves-∙ p q)

\end{code}
