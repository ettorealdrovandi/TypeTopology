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

{--------------------------------------------}

silly : {X : 𝓤 ̇  } {x y z : X} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
      → p ∙ q ≡ r
      → q ≡ p ⁻¹ ∙ r
silly refl refl refl refl = refl

silly-converse : {X : 𝓤 ̇  } {x y z : X} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
               → q ≡ p ⁻¹ ∙ r
               → p ∙ q ≡ r
silly-converse p q refl refl = (right-inverse p) ⁻¹

another-silly : {X : 𝓤 ̇  } {x y : X} (p q : x ≡ y)
              → p ∙ (p ⁻¹ ∙ q) ≡ q
another-silly p refl = (right-inverse p) ⁻¹

foo2 : {X : 𝓤 ̇  } {x y z : X} (p : x ≡ y) (q : y ≡ z) (r : x ≡ z)
     → (q ≡ p ⁻¹ ∙ r) → p ∙ q ∙ r ⁻¹ ≡ refl
foo2 refl q refl refl = refl

foo : {X : 𝓤 ̇  } {x y : X} (p : x ≡ y) (q : x ≡ y)
    → (refl ≡ p ⁻¹ ∙ q) ≃ (refl ≡ p ∙ q ⁻¹)
foo p refl = ≃-sym γ
 where
  γ : (refl ≡ p) ≃ (refl ≡ p ⁻¹)
  γ = (ap _⁻¹)
    , (embedding-embedding' _⁻¹ (equivs-are-embeddings _⁻¹ ⁻¹-is-equiv) refl p)

{-----------------------------------------------}

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

  ≈-is-prop-valued : is-prop-valued _≈_
  ≈-is-prop-valued _ _ = ∃-is-prop

  _≈'_ : based-paths x y → based-paths x y → 𝓥 ̇
  (p , q) ≈' (p' , q') = ∥ φ (p ⁻¹ ∙ p') ≡ q ⁻¹ ∙ q' ∥

  ≈'-is-prop-valued : is-prop-valued _≈'_
  ≈'-is-prop-valued _ _ = ∥∥-is-prop


  ≈-implies-≈' : {b c : based-paths x y} → b ≈ c → b ≈' c
  ≈-implies-≈' {(p , q)} {(p' , q')} = ∥∥-functor γ
   where
    γ : (Σ l ꞉ x₀ ≡ x₀ , (p ∙ l ≡ p') × (q ∙ φ l ≡ q'))
      → φ (p ⁻¹ ∙ p') ≡ q ⁻¹ ∙ q'
    γ (l , u , v) = silly q (φ (p ⁻¹ ∙ p')) q' e'
     where
      e : l ≡ p ⁻¹ ∙ p'
      e = silly p l p' u
      e' = q ∙ φ (p ⁻¹ ∙ p') ≡⟨ ap (λ - → q ∙ φ -) (e ⁻¹) ⟩
           q ∙ φ l           ≡⟨ v ⟩
           q'                ∎

  ≈'-implies-≈ : {b c : based-paths x y} → b ≈' c → b ≈ c
  ≈'-implies-≈ {(p , q)} {(p' , q')} = ∥∥-functor γ
   where
    γ : φ (p ⁻¹ ∙ p') ≡ q ⁻¹ ∙ q'
      → Σ l ꞉ x₀ ≡ x₀ , (p ∙ l ≡ p') × (q ∙ φ l ≡ q')
    γ e = (p ⁻¹ ∙ p') , another-silly p p'
                      , silly-converse q (φ (p ⁻¹ ∙ p')) q' e

  ≈-and-≈'-coincide : {b c : based-paths x y} → (b ≈ c) ≃ (b ≈' c)
  ≈-and-≈'-coincide {b} {c} =
   logically-equivalent-props-are-equivalent
    (≈-is-prop-valued b c)
    (≈'-is-prop-valued b c)
    ≈-implies-≈'
    ≈'-implies-≈

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

 ≈₀-normal-form : {y : Y} {p : x₀ ≡ x₀} {q : y ≡ y₀}
                → (p , q) ≈ (refl , (q ∙ φ (p ⁻¹)))
 ≈₀-normal-form {y} {p} {q} = ∣ (p ⁻¹) , ((right-inverse p) ⁻¹) , refl ∣

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

 ι-fiber-equiv : is-groupoid Y → (s : domain ι) → fiber ι (ι s) ≃ domain ι
 ι-fiber-equiv Y-is-grpd (y , q) =
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
       ((refl , q') ≈ (refl , q))           ≃⟨ II'      ⟩
       ((refl , q') ≈' (refl , q))          ≃⟨ ≃-refl _ ⟩
       ∥ φ refl ≡ q' ⁻¹ ∙ q ∥               ≃⟨ III'     ⟩
       (φ refl ≡ q' ⁻¹ ∙ q)                 ≃⟨ IV'      ⟩
       (refl ≡ q' ⁻¹ ∙ q)                   ≃⟨ V'       ⟩
       (refl ≡ q' ∙ q ⁻¹)                   ■
        where
         I'   = ≃-sym (≈-coincides-with-quotient-equality ≋)
         II'  = ≈-and-≈'-coincide
         III' = prop-is-equivalent-to-its-truncation (Y-is-grpd _ _)
         IV'  = ≡-cong-l _ _ φ-preserves-refl
         V'   = foo q' q

 ι-is-embedding : is-groupoid Y → is-embedding ι
 ι-is-embedding Y-is-grpd = embedding-criterion ι γ
  where
   γ : (s : domain ι) → is-prop (fiber ι (ι s))
   γ s = equiv-to-prop ⦅1⦆ ⦅2⦆
    where
     ⦅1⦆ : fiber ι (ι s) ≃ domain ι
     ⦅1⦆ = ι-fiber-equiv Y-is-grpd s
     ⦅2⦆ : is-prop (domain ι)
     ⦅2⦆ = singletons-are-props (singleton-types'-are-singletons y₀)

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
   baz x x' = ∥∥-rec₂ ∥∥-is-prop γ (η/-is-surjection (pr₂ (κ x))) (η/-is-surjection (pr₂ (κ x')))
    where
     γ : (Σ b  ꞉ based-paths x  (f x)  , η/ ≋ b  ≡ pr₂ (κ x) )
       → (Σ b' ꞉ based-paths x' (f x') , η/ ≋ b' ≡ pr₂ (κ x'))
       → ∥ Σ pₓ ꞉   x ≡ x₀ , Σ pₓ' ꞉   x' ≡ x₀
         , Σ qₓ ꞉ f x ≡ y₀ , Σ qₓ' ꞉ f x' ≡ y₀
         , ap f ∼ ⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝ ∥
     γ ((pₓ , qₓ) , e) ((pₓ' , qₓ') , e') = ∣ pₓ , pₓ' , qₓ , qₓ' , blah ∣
      where
       blah : (p : x ≡ x') → ap f p ≡ (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) p
       blah refl = ∥∥-rec (Y-grpd (f x) (f x)) bzzz
                          (≈-implies-≈' (/-is-effective ≋ (e ∙ e' ⁻¹)))
        where
         bzzz : φ (pₓ ⁻¹ ∙ pₓ') ≡ qₓ ⁻¹ ∙ qₓ'
              → ap f refl ≡ (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) refl
         bzzz φ-eq = refl                                     ≡⟨ I    ⟩
                     qₓ ∙ φ (pₓ ⁻¹ ∙ pₓ') ∙ qₓ' ⁻¹            ≡⟨ refl ⟩
                     (⌜ E₂ qₓ qₓ' ⌝ ∘ φ ∘ ⌜ E₁ pₓ pₓ' ⌝) refl ∎
          where
           I = (foo2 qₓ (φ (pₓ ⁻¹ ∙ pₓ')) qₓ' φ-eq) ⁻¹

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

-- Final proof

delooping-of-group-isomorphism = γ
 where
  γ : {X : 𝓤 ̇  } {Y : 𝓥 ̇  }
    → funext (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)
    → is-connected X
    → is-connected Y
    → is-groupoid Y
    → (x₀ : X) (y₀ : Y)
    → (φ : (x₀ ≡ x₀) → (y₀ ≡ y₀))
    → is-equiv φ
    → ((p q : (x₀ ≡ x₀)) → φ (p ∙ q) ≡ φ p ∙ φ q)
    → X ≃ Y
  γ fe X-con Y-con Y-grpd x₀ y₀ φ φ-is-equiv φ-preserves-∙ =
     f          fe Y-grpd X-con
   , f-is-equiv fe Y-grpd X-con Y-con
   where
    open construction x₀ y₀ φ φ-is-equiv (λ {p} {q} → φ-preserves-∙ p q)

\end{code}
