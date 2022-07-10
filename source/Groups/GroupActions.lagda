--------------------------------------------------------------------------------
Ettore Aldrovandi aldrovandi@math.fsu.edu
Keri D'Angelo kd349@cornell.edu

June 2022
--------------------------------------------------------------------------------

Group actions on sets and Torsors, following the UniMath blueprint. We
add a couple of things:

1. actions give homomorphisms into groups of automorphisms and
   viceversa.
2. pullbacks of actions.
3. G Sets
4. Different (equivalent) definitions of G-torsor


\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}

open import SpartanMLTT
open import UF-Base hiding (_≈_)
open import UF-Subsingletons
open import UF-Powerset
open import UF-Equiv
open import UF-EquivalenceExamples
open import UF-Embeddings
open import UF-Univalence
open import UF-Equiv-FunExt
open import UF-FunExt
open import UF-UA-FunExt
open import UF-Subsingletons-FunExt
open import UF-Retracts
open import UF-Classifiers

open import Groups renaming (_≅_ to _≣_)
open import Groups.Groups-Supplement

module Groups.GroupActions where

module _ (G : Group 𝓤) where

  action-structure : 𝓤 ̇ → 𝓤 ̇
  action-structure X = ⟨ G ⟩ → X → X

  action-axioms : (X : 𝓤 ̇) → action-structure X → 𝓤 ̇
  action-axioms X _·_ = is-set X ×
                        ((g h : ⟨ G ⟩)(x : X) → (g ·⟨ G ⟩ h) · x ≡ g · (h · x)) ×
                        ((x : X) → (unit G) · x ≡ x)

  Action-structure : 𝓤 ̇ → 𝓤 ̇
  Action-structure X = Σ _·_ ꞉ action-structure X , (action-axioms X _·_)

  Action : 𝓤 ⁺ ̇
  Action = Σ X ꞉ 𝓤 ̇ , Action-structure X


  action-carrier : Action → 𝓤 ̇
  action-carrier (X , _ ) = X

  action-op : (𝕏 : Action) → action-structure ⟨ 𝕏 ⟩
  action-op (X , op , _) = op

  syntax action-op 𝕏 g x = g ◂⟨ 𝕏 ⟩ x

  carrier-is-set : (𝕏 : Action) → is-set (action-carrier 𝕏)
  carrier-is-set (X , op , i , _) = i

  action-assoc : (𝕏 : Action) (g h : ⟨ G ⟩) (x : ⟨ 𝕏 ⟩) →
                 (action-op 𝕏) (g ·⟨ G ⟩ h) x ≡ (action-op 𝕏) g ((action-op 𝕏) h x)
  action-assoc (X , op , i , a , u) = a

  action-unit : (𝕏 : Action) (x : ⟨ 𝕏 ⟩) →
                (action-op 𝕏) (unit G) x ≡ x
  action-unit (X , op , i , a , u) = u

  action-tofun : {𝕏 : Action} (g : ⟨ G ⟩) → ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
  action-tofun {𝕏} g = λ x → action-op 𝕏 g x

  action-to-fun = action-tofun

  action-tofun-is-equiv : {𝕏 : Action} (g : ⟨ G ⟩) →
                          is-equiv (action-tofun {𝕏} g)
  action-tofun-is-equiv {𝕏} g =
            (f⁻¹ , λ x → (f (f⁻¹ x)                   ≡⟨ (action-assoc 𝕏 _ _ _) ⁻¹ ⟩
                          (g ·⟨ G ⟩ (inv G g)) ◂⟨ 𝕏 ⟩ x ≡⟨ ap (λ v → v ◂⟨ 𝕏 ⟩ x) (inv-right G g) ⟩
                          (unit G) ◂⟨ 𝕏 ⟩ x            ≡⟨ action-unit 𝕏 x  ⟩
                           x ∎)) ,
            (f⁻¹ , λ x → (f⁻¹ (f x)                   ≡⟨ (action-assoc 𝕏 _ _ _) ⁻¹ ⟩
                          ((inv G g) ·⟨ G ⟩ g) ◂⟨ 𝕏 ⟩ x ≡⟨ ap (λ v → v ◂⟨ 𝕏 ⟩ x) (inv-left G g) ⟩
                          (unit G) ◂⟨ 𝕏 ⟩ x            ≡⟨ action-unit 𝕏 x ⟩
                           x  ∎))
    where
      f : ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
      f = action-tofun {𝕏} g

      f⁻¹ : ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
      f⁻¹ = action-tofun {𝕏} (inv G g)

  action-to-fun-is-equiv = action-tofun-is-equiv

  action-to-Aut : {𝕏 : Action} (g : ⟨ G ⟩) → Aut ⟨ 𝕏 ⟩
  action-to-Aut {𝕏} g = (action-to-fun {𝕏} g) , action-to-fun-is-equiv {𝕏} g

  -- same as in UniMath
  left-mult = action-to-fun
  right-mult : {𝕏 : Action} (x : ⟨ 𝕏 ⟩) → ⟨ G ⟩ → ⟨ 𝕏 ⟩
  right-mult {𝕏} x = λ g → g ◂⟨ 𝕏 ⟩ x
  ----------------------------------

  -- the total action map is often used, especiall for torsors
  ------------------------------------------------------------
  mult : {𝕏 : Action} →
         ⟨ G ⟩ × ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩ × ⟨ 𝕏 ⟩
  mult {𝕏} (g , x) = g ◂⟨ 𝕏 ⟩ x , x

\end{code}

In this submodule we prove that an action as defined above induces a
homomorphism from the group ot the automorphism group of the carrier
set. It requires funext 𝓤 𝓤 because Aut (X) (as a group)
does. Conversely, a homomorphism to Aut (X) gives an action.

\begin{code}
  module automorphism (fe : funext 𝓤 𝓤) where

    open import Groups.Aut

    module _ (𝕏 : Action) where

      private
        X : 𝓤 ̇
        X = ⟨ 𝕏 ⟩
        i : is-set X
        i = carrier-is-set 𝕏
        _·_ : ⟨ G ⟩ → X → X
        _·_ = action-op 𝕏

        j : is-set (Aut X)
        j = is-set-Aut fe X i

        gr-s-X : _
        gr-s-X = Group-structure-Aut fe X i

      is-hom-action-to-fun : is-hom G (Aut X , gr-s-X) (action-to-Aut {𝕏})
      is-hom-action-to-fun {g} {h} =
                           to-Σ-≡ ((dfunext fe (action-assoc 𝕏 g h)) ,
                             (being-equiv-is-prop'' fe (λ x → g · (h · x)) _ _))

    module _ (X : 𝓤 ̇) (i : is-set X) (σ : ⟨ G ⟩ → Aut X) where
      
      private
        j : is-set (Aut X)
        j = is-set-Aut fe X i

        gr-s-X : _
        gr-s-X = Group-structure-Aut fe X i

      hom-to-Aut-gives-action : is-hom G (Aut X , gr-s-X) σ → Action
      hom-to-Aut-gives-action is = X , ((λ g → pr₁ (σ g)) ,
                              (i , (λ g h → happly (ap pr₁ (is {g} {h}))) ,
                               λ x → ( pr₁ (σ (unit G)) x            ≡⟨ happly (ap pr₁ t) x ⟩
                                       pr₁ (unit (Aut X , gr-s-X)) x ≡⟨ happly' id id refl x ⟩
                                       x ∎ ) ) )
        where
          t : σ (unit G) ≡ unit (Aut X , gr-s-X)
          t = homs-preserve-unit G (Aut X , gr-s-X) σ is

    
\end{code}

Resuming the general theory, the group action axioms form a proposition
and the Action-structure is a set.

\begin{code}
  action-axioms-is-prop : funext 𝓤 𝓤 →
                          (X : 𝓤 ̇) →
                          (_·_ : action-structure X) →
                          is-prop (action-axioms X _·_)
  action-axioms-is-prop fe X _·_ s = γ s
    where
      i : is-set X
      i = pr₁ s

      γ : is-prop (action-axioms X _·_)
      γ = ×-is-prop (being-set-is-prop fe)
                    (×-is-prop (Π-is-prop fe
                                  (λ g → Π-is-prop fe
                                     (λ h → Π-is-prop fe
                                        (λ x → i))))
                        (Π-is-prop fe (λ x → i)))


  Action-structure-is-set : funext 𝓤 𝓤 →
                            (X : 𝓤 ̇) →
                            is-set (Action-structure X)
  Action-structure-is-set fe X {s} = γ {s}
    where
      i : is-set X
      i = pr₁ (pr₂ s)

      γ : is-set (Action-structure X)
      γ = Σ-is-set (Π-is-set fe
                      (λ g → Π-is-set fe
                               (λ x → i)))
            λ op → props-are-sets (action-axioms-is-prop fe X op)

\end{code}


Equivariant maps.

\begin{code}

  is-equivariant : {𝕏 𝕐 : Action} (f : ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) → 𝓤 ̇
  is-equivariant {𝕏} {𝕐} f = ∀ g x → f (g · x) ≡ g * (f x)
    where
      _·_ = action-op 𝕏
      _*_ = action-op 𝕐


  is-equivariant-is-prop : funext 𝓤 𝓤 →
                           {𝕏 𝕐 : Action} → (f : ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) →
                           is-prop (is-equivariant {𝕏} {𝕐} f)
  is-equivariant-is-prop fe {𝕏} {𝕐} f s = γ s
    where
      i : is-set (action-carrier 𝕐)
      i = carrier-is-set 𝕐
      
      γ : is-prop (is-equivariant {𝕏} {𝕐} f)
      γ = Π-is-prop fe
                    (λ g → Π-is-prop fe
                                     (λ x → i))

  is-equivariant-comp : {𝕏 𝕐 ℤ : Action} →
                        (p : ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) (i : is-equivariant {𝕏} {𝕐} p) →
                        (q : ⟨ 𝕐 ⟩ → ⟨ ℤ ⟩) (j : is-equivariant {𝕐} {ℤ} q) → 
                        (is-equivariant {𝕏} {ℤ} (q ∘ p))
  is-equivariant-comp {𝕏} {𝕐} {ℤ} p i q j g x = q (p (g · x)) ≡⟨ ap q (i g x) ⟩
                                                q (g * (p x)) ≡⟨ j g (p x) ⟩
                                                g ✵ (q (p x)) ∎
    where
      _·_ = action-op 𝕏
      _*_ = action-op 𝕐
      _✵_ = action-op ℤ

\end{code}

The following "fundamental" fact from UniMath is that an
identification p : ⟨ 𝕏 ⟩ ≡ ⟨ 𝕐 ⟩ between the carriers of two actions
essentially gives rise to an equivariant map. More precisely,
equivariance of the identity is the same as the identification of the
structures.

\begin{code}

  ≡-is-equivariant : funext 𝓤 𝓤 →
                     {𝕏 𝕐 : Action} →
                     (p : ⟨ 𝕏 ⟩ ≡ ⟨ 𝕐 ⟩) →
                     (transport Action-structure p (pr₂ 𝕏)  ≡ pr₂ 𝕐 ) ≃ 
                     is-equivariant {𝕏} {𝕐} (idtofun ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p)
  pr₁ (≡-is-equivariant fe {X , as} {.X , .as} refl) refl = λ g x → refl
  pr₂ (≡-is-equivariant fe {X , as} {.X , as'} refl) =
    logically-equivalent-props-give-is-equiv
      is (is-equivariant-is-prop fe {X , as} {X , as'} id)
        (pr₁ (≡-is-equivariant fe refl))
        λ i → to-Σ-≡ ((γ i) , action-axioms-is-prop fe X _·'_ _ _)
      where
        _·_ _·'_ : action-structure X
        _·_  = pr₁ as
        _·'_ = pr₁ as'

        is : is-prop (as ≡ as')
        is = Action-structure-is-set fe X {as} {as'}

        γ : is-equivariant {X , as} {X , as'} id → _·_ ≡ _·'_
        γ = λ i → dfunext fe
                  (λ g → dfunext fe λ x → i g x)
\end{code}

The above function is called is_equivariant_identity in UniMath.

\begin{code}

  Action-Map : (𝕏 𝕐 : Action) → 𝓤  ̇
  Action-Map 𝕏 𝕐 = Σ f ꞉ (⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩) , is-equivariant {𝕏} {𝕐} f

  underlying-function : {𝕏 𝕐 : Action} (u : Action-Map 𝕏 𝕐) → ⟨ 𝕏 ⟩ → ⟨ 𝕐 ⟩
  underlying-function u = pr₁ u

  equivariance : {𝕏 𝕐 : Action} (u : Action-Map 𝕏 𝕐) → 
                 is-equivariant {𝕏} {𝕐} (underlying-function {𝕏} {𝕐} u)
  equivariance u = pr₂ u


  Action-Map-is-set : funext 𝓤 𝓤 →
                      (𝕏 𝕐 : Action) →
                      is-set (Action-Map 𝕏 𝕐)
  Action-Map-is-set fe 𝕏 𝕐 {s} = γ {s}
    where
      γ : is-set (Action-Map 𝕏 𝕐)
      γ = Σ-is-set (Π-is-set fe
                     (λ u → carrier-is-set 𝕐))
                   λ f → props-are-sets (is-equivariant-is-prop fe {𝕏} {𝕐} f)

  compose-Action-Map : {𝕏 𝕐 ℤ : Action} →
                       (Action-Map 𝕏 𝕐) → (Action-Map 𝕐 ℤ) →
                       (Action-Map 𝕏 ℤ)
  compose-Action-Map {𝕏} {𝕐} {ℤ} (p , i) (q , j) =
                     (q ∘ p) , (is-equivariant-comp {𝕏} {𝕐} {ℤ} p i q j)

  Action-Iso : (𝕏 𝕐 : Action) → 𝓤 ̇
  Action-Iso 𝕏 𝕐 = Σ f ꞉ ⟨ 𝕏 ⟩ ≃ ⟨ 𝕐 ⟩ , is-equivariant {𝕏} {𝕐} (eqtofun f)

  Action-Iso-is-set : funext 𝓤 𝓤 →
                      (𝕏 𝕐 : Action) →
                      is-set (Action-Iso 𝕏 𝕐)
  Action-Iso-is-set fe 𝕏 𝕐 {s} = γ {s}
    where
      γ : is-set (Action-Iso 𝕏 𝕐)
      γ = Σ-is-set (Σ-is-set (Π-is-set fe (λ _ → carrier-is-set 𝕐))
                             λ f → props-are-sets (being-equiv-is-prop'' fe f))
                   λ u → props-are-sets (is-equivariant-is-prop fe {𝕏} {𝕐} (pr₁ u))

  underlying-iso : {𝕏 𝕐 : Action} → Action-Iso 𝕏 𝕐 → ⟨ 𝕏 ⟩ ≃ ⟨ 𝕐 ⟩
  underlying-iso u = pr₁ u
                   
  underlying-iso-is-embedding : funext 𝓤 𝓤 →
                                {𝕏 𝕐 : Action} →
                                is-embedding (underlying-iso {𝕏} {𝕐} )
  underlying-iso-is-embedding fe {𝕏} {𝕐} =
    pr₁-is-embedding (λ f → is-equivariant-is-prop fe {𝕏} {𝕐} (pr₁ f))
                           
  underlying-iso-injectivity : funext 𝓤 𝓤 → 
                               {𝕏 𝕐 : Action} →
                               (u v : Action-Iso 𝕏 𝕐) →
                               (u ≡ v) ≃ (underlying-iso {𝕏} {𝕐} u ≡ underlying-iso {𝕏} {𝕐} v)
  underlying-iso-injectivity fe {𝕏} {𝕐} u v =
    ≃-sym (embedding-criterion-converse
             (underlying-iso {𝕏} {𝕐})
             (underlying-iso-is-embedding fe {𝕏} {𝕐}) u v) 

  
  underlying-Action-Map : {𝕏 𝕐 : Action} → Action-Iso 𝕏 𝕐 →
                          Action-Map 𝕏 𝕐
  underlying-Action-Map ((f , _) , is) = f , is

  id-Action-Iso : (𝕏 : Action) → Action-Iso 𝕏 𝕏
  id-Action-Iso 𝕏 = (id , (id-is-equiv ⟨ 𝕏 ⟩)) , (λ g x → refl)

  ≡-to-Action-Iso : {𝕏 𝕐 : Action} →
                    𝕏 ≡ 𝕐 → Action-Iso 𝕏 𝕐
  ≡-to-Action-Iso {𝕏} {𝕐} p = transport (Action-Iso 𝕏) p (id-Action-Iso 𝕏)

  ≡-to-Action-Iso₁ : {𝕏 𝕐 : Action} →
                     𝕏 ≡ 𝕐 → Action-Iso 𝕏 𝕐
  ≡-to-Action-Iso₁ {𝕏} {.𝕏} refl = id-Action-Iso 𝕏

  compose-Action-Iso : {𝕏 𝕐 ℤ : Action} →
                       Action-Iso 𝕏 𝕐 → Action-Iso 𝕐 ℤ →
                       Action-Iso 𝕏 ℤ
  compose-Action-Iso {𝕏} {𝕐} {ℤ} (f , i) (g , j) =
                     (f ● g) , (is-equivariant-comp {𝕏} {𝕐} {ℤ} (pr₁ f) i (pr₁ g) j)

  compose-Action-Iso-id : funext 𝓤 𝓤 → 
                          {𝕏 𝕐 : Action} → (u : Action-Iso 𝕏 𝕐) →
                          compose-Action-Iso {𝕏} {𝕐} {𝕐} u (id-Action-Iso 𝕐) ≡ u
  compose-Action-Iso-id fe {𝕏} {𝕐} u = to-subtype-≡
                           (λ f → is-equivariant-is-prop fe {𝕏} {𝕐} (eqtofun f))
                           (≃-refl-right' fe fe fe (pr₁ u))

  compose-id-Action-Iso : funext 𝓤 𝓤 →
                          {𝕏 𝕐 : Action} → (u : Action-Iso 𝕏 𝕐) →
                          compose-Action-Iso {𝕏} {𝕏} {𝕐} (id-Action-Iso 𝕏) u ≡ u
  compose-id-Action-Iso fe {𝕏} {𝕐} u = to-subtype-≡
                           (λ f → is-equivariant-is-prop fe {𝕏} {𝕐} (eqtofun f))
                           (≃-refl-left' fe fe fe (pr₁ u))
\end{code}

Univalence for group actions. The abstract clause below is to speed up
type-checking.

\begin{code}

  module _ (ua : is-univalent 𝓤) where

    private
      fe : funext 𝓤 𝓤
      fe = univalence-gives-funext ua

    Id-equiv-Action-Iso_prelim : (𝕏 𝕐 : Action) →
                              (𝕏 ≡ 𝕐) ≃ (Action-Iso 𝕏 𝕐)
    Id-equiv-Action-Iso_prelim 𝕏 𝕐 = ≃-comp (Φ , ll) (Ψ , ii)
      where
        T : (𝕏 𝕐 : Action) → (𝓤 ⁺) ̇
        T 𝕏 𝕐 = Σ u ꞉ ⟨ 𝕏 ⟩ ≡ ⟨ 𝕐 ⟩ , transport Action-structure u (pr₂ 𝕏) ≡ pr₂ 𝕐

        Φ : (𝕏 ≡ 𝕐) → T 𝕏 𝕐
        Φ = from-Σ-≡ 

        Φ' : T 𝕏 𝕐 → (𝕏 ≡ 𝕐)
        Φ' = to-Σ-≡

        Ψ : T 𝕏 𝕐 → Action-Iso 𝕏 𝕐
        Ψ (p , is) = (idtoeq ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p) , pr₁ (≡-is-equivariant fe {𝕏} {𝕐} p) is

        abstract
          Ψ' : Action-Iso 𝕏 𝕐 → T 𝕏 𝕐
          Ψ' (e , is) = p , pr₁ (≃-sym (≡-is-equivariant fe {𝕏} {𝕐} p)) i
            where
              p : ⟨ 𝕏 ⟩ ≡ ⟨ 𝕐 ⟩
              p = eqtoid ua ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ e
              i : is-equivariant {𝕏} {𝕐} (idtofun ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p)
              i = transport (is-equivariant {𝕏} {𝕐}) (t ⁻¹) is
                where
                  t : idtofun ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p ≡ eqtofun e
                  t = idtofun-eqtoid ua e

          Ψ'Ψ-id : (σ : T 𝕏 𝕐) → Ψ' (Ψ σ) ≡ σ
          Ψ'Ψ-id (p , is) = to-Σ-≡ (eqtoid-idtoeq ua ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ p ,
                                   Action-structure-is-set fe _ _ _)

          ΨΨ'-id : (u : Action-Iso 𝕏 𝕐) → Ψ (Ψ' u) ≡ u
          ΨΨ'-id (e , is) = to-Σ-≡ ((idtoeq-eqtoid ua ⟨ 𝕏 ⟩ ⟨ 𝕐 ⟩ e) ,
                                   (is-equivariant-is-prop fe {𝕏} {𝕐} _ _ _))
        ii : is-equiv Ψ
        ii = qinvs-are-equivs Ψ inv-Ψ
          where
            inv-Ψ : invertible Ψ
            inv-Ψ = Ψ' , (Ψ'Ψ-id , ΨΨ'-id)
            
        ll : is-equiv Φ
        ll = qinvs-are-equivs Φ inv-Φ
          where
            inv-Φ : invertible Φ
            inv-Φ = Φ' , (tofrom-Σ-≡ , fromto-Σ-≡)


    ≡-to-Action-Iso-is-equiv : {𝕏 𝕐 : Action} →
                               is-equiv (≡-to-Action-Iso {𝕏} {𝕐})
    ≡-to-Action-Iso-is-equiv {𝕏} {𝕐} = equiv-closed-under-∼'
                             (pr₂ (Id-equiv-Action-Iso_prelim 𝕏 𝕐)) h
      where
        f = pr₁ (Id-equiv-Action-Iso 𝕏 prelim 𝕐)
        g = ≡-to-Action-Iso
        h : f ∼ g
        h refl = refl


    Id-equiv-Action-Iso : (𝕏 𝕐 : Action) →
                       (𝕏 ≡ 𝕐) ≃ (Action-Iso 𝕏 𝕐)
    Id-equiv-Action-Iso 𝕏 𝕐 = ≡-to-Action-Iso , ≡-to-Action-Iso-is-equiv

\end{code}

When explicitly expressed in terms of a group G, the type Action is
just that of G-Sets, so we also use this notation.

\begin{code}

_Sets : Group 𝓤 → 𝓤 ⁺ ̇
G Sets = Action G

\end{code}

For a group homomorphism φ : H → G the action pulls back, because it
is a functor from the one-object category G[1] to sets.

\begin{code}

action-pullback : {H G : Group 𝓤} →
                  (f : ⟨ H ⟩ → ⟨ G ⟩) → is-hom H G f →
                  G Sets → H Sets
action-pullback {H = H} {G} f i ρ = (action-carrier G ρ) ,
                (λ h x → (f h) · x) ,
                  (carrier-is-set G ρ) ,
                    ((λ h h₁ → λ x → (f (h ·⟨ H ⟩ h₁) · x       ≡⟨ ap (_· x) i ⟩
                                      ((f h) ·⟨ G ⟩ (f h₁)) · x ≡⟨ action-assoc G ρ _ _ _ ⟩
                                      (f h · (f h₁ · x)) ∎  )) ,
                     λ x → (f (unit H) · x ≡⟨ ap (_· x) p ⟩
                            unit G · x     ≡⟨ action-unit G ρ x ⟩
                            x  ∎))
  where
    _·_ = action-op G ρ
    p  = homs-preserve-unit H G f i
\end{code}

TODO: The left adjoint, that is, the map H Sets → G Sets along the
homomorphism H → G. It uses the quotient module.

TORSORS.

A torsor is a G-Set with nonempty underlying carrier and such that for
any x : X the right-multiplication map λ g → g · x is an equivalence.

This can be equivalently formulated by saying that the "shear" map
⟨ G ⟩ × ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩ × ⟨ 𝕏 ⟩ is an equivalence.

Those two formulations are equivalent (both being props).

\begin{code}

is-torsor : (G : Group 𝓤) (𝕏 : G Sets) → 𝓤  ̇
is-torsor G (X , a) = is-nonempty X ×
                     ((x : X) → is-equiv (right-mult G {X , a} x))

is-torsor-is-prop : funext 𝓤 𝓤 → funext 𝓤 𝓤₀ →
                    (G : Group 𝓤) (𝕏 : G Sets) →
                    is-prop (is-torsor G 𝕏)
is-torsor-is-prop fe fe₀ G 𝕏 = ×-is-prop (negations-are-props fe₀)
          (Π-is-prop fe (λ x → being-equiv-is-prop'' fe (right-mult G {𝕏} x)))


is-torsor₁ : (G : Group 𝓤) (𝕏 : G Sets) → 𝓤 ̇
is-torsor₁ G 𝕏 = is-nonempty ⟨ 𝕏 ⟩ × is-equiv (mult G {𝕏})

is-torsor₁-is-prop : funext 𝓤 𝓤 → funext 𝓤 𝓤₀ →
                     (G : Group 𝓤) (𝕏 : G Sets) →
                     is-prop (is-torsor₁ G 𝕏)
is-torsor₁-is-prop fe fe₀ G 𝕏 = ×-is-prop (negations-are-props fe₀)
                   (being-equiv-is-prop'' fe (mult G {𝕏}))

torsor→torsor₁ : {G : Group 𝓤} (𝕏 : G Sets) →
                 is-torsor G 𝕏 → is-torsor₁ G 𝕏
torsor→torsor₁ {𝓤} {G} (X , a) (n , e) = n , ee
  where
    ee : is-equiv (mult G {X , a})
    ee = (u , ε) , v , η
      where
        u : X × X → ⟨ G ⟩ × X
        u ( y , x) = (pr₁ (pr₁ (e x)) y) , x

        ε : (mult G {X , a}) ∘ u ∼ id
        ε (y , x) = to-×-≡ (pr₂ (pr₁ (e x)) y) refl

        v : X × X → ⟨ G ⟩ × X
        v (y , x) = pr₁ (pr₂ (e x)) y , x

        η : v ∘ (mult G {X , a}) ∼ id
        η (g , x) = to-×-≡ (pr₂ (pr₂ (e x)) g) refl

torsor₁→torsor : {G : Group 𝓤} (𝕏 : G Sets) →
                 is-torsor₁ G 𝕏 → is-torsor G 𝕏
torsor₁→torsor {𝓤} {G} (X , a) (n , e) = n , ee
  where
    ee : (x : X) → is-equiv (right-mult G {X , a} x)
    ee x = (u , ε) , v , η
      where
        m : ⟨ G ⟩ × X → X × X
        m = mult G {X , a}
        r : ⟨ G ⟩ → X
        r = right-mult G {X , a} x

        ri li : X × X → ⟨ G ⟩ × X
        ri = pr₁ (pr₁ e)
        li = pr₁ (pr₂ e)

        e-ri : m ∘ ri ∼ id
        e-ri = pr₂ (pr₁ e)

        li-e : li ∘ m ∼ id
        li-e = pr₂ (pr₂ e)

        γ : (g : ⟨ G ⟩) → m (g , x) ≡ r g , x
        γ g = refl

        u : X → ⟨ G ⟩
        u y = pr₁ (ri (y , x))

        ε : r ∘ u ∼ id
        ε y = ap pr₁ q ⁻¹
          where
            p : pr₂ ( ri (y , x) ) ≡ x
            p = ap pr₂ (e-ri (y , x))

            q : y , x ≡ r (u y) , x
            q = y , x                      ≡⟨ e-ri (y , x) ⁻¹ ⟩
                m (ri (y , x))             ≡⟨ ap m refl ⟩
                m (u y , pr₂ (ri (y , x))) ≡⟨ ap (λ v → m (u y , v)) p ⟩
                m (u y , x)                ≡⟨ γ (u y) ⟩
                r (u y) , x ∎

        v : X → ⟨ G ⟩
        v y = pr₁ (li (y , x))

        η : v ∘ r ∼ id
        η g = ap pr₁ q ⁻¹
          where
            p : pr₂ (li (r g , x)) ≡ x
            p = ap pr₂ (li-e (g , x))

            q : g , x ≡ v (r g) , x
            q = g , x                        ≡⟨ li-e (g , x) ⁻¹ ⟩
                li (m (g , x))               ≡⟨ ap li (γ g) ⟩
                li (r g , x)                 ≡⟨ refl ⟩
                v (r g) , pr₂ (li (r g , x)) ≡⟨ ap (λ z → v (r g) , z) p ⟩
                v (r g) , x ∎
\end{code}


The type of G-Torsors.

\begin{code}

TORS Tors Torsor : (G : Group 𝓤) → (𝓤 ⁺) ̇
TORS G = Σ 𝕏 ꞉ Action G , is-torsor G 𝕏
Tors = TORS
Torsor = TORS

TORS' Tors' Torsor' : (G : Group 𝓤) → (𝓤 ⁺) ̇
TORS' {𝓤} G = Σ X ꞉ 𝓤 ̇ , Σ a ꞉ Action-structure G X , is-torsor G (X , a)
Tors' = TORS'
Torsor' = TORS'

torsor-equivalent-defs : {G : Group 𝓤} → TORS G ≃ TORS' G
torsor-equivalent-defs = Σ-assoc

underlying-action : {G : Group 𝓤} → (X : Tors G) →
                    Action G
underlying-action X = pr₁ X

torsor-carrier : {G : Group 𝓤} (X : Tors G) → 𝓤 ̇
torsor-carrier X = ⟨ pr₁ X  ⟩

torsor-prop : {G : Group 𝓤} (X : Tors G) → is-torsor G (pr₁ X)
torsor-prop X = pr₂ X

torsor-nonempty : {G : Group 𝓤} (X : Tors G) → is-nonempty (pr₁ (pr₁ X))
torsor-nonempty {𝓤} {G} X = pr₁ (torsor-prop {𝓤} {G} X)

torsor-splitting : {G : Group 𝓤} (X : Tors G) → 
                   ((x : ⟨ pr₁ X ⟩) → is-equiv (right-mult G {pr₁ X} x))
torsor-splitting {𝓤} {G} X = pr₂ (torsor-prop {𝓤} {G} X)

torsor-splitting₁ : {G : Group 𝓤} (X : Tors G) →
                    is-equiv (mult G {pr₁ X})
torsor-splitting₁ {G = G} X = pr₂ (torsor→torsor₁ {G = G} (pr₁ X) (pr₂ X))

torsor-to-equiv : {G : Group 𝓤} (X : Tors G) →
                  (x : torsor-carrier {G = G} X) → ⟨ G ⟩ ≃ (torsor-carrier {G = G} X)
torsor-to-equiv {G = G} X x = (right-mult G {pr₁ X} x) , torsor-splitting {G = G} X x

\end{code}

The equivalence G × X → X × X is the counterpart to the classical fact
that the "shear" map G × X → X × X given by (g , x) ↦ (g · x , x) is
an isomorphism. In classical geometry this implies that the inverse
also has x as its second component. In other words, pr₂ = x.

Not so here, as highligheted by the convoluted proof above where an
explicit proof that pr₂ ( inverse (mult) (y , x)) ≡ x was needed.  We
codify this fact, as it will be useful elsewhere.

\begin{code}

torsor-rinv-mult torsor-linv-mult : (G : Group 𝓤) (X : Tors G) →
                                    (⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩)
torsor-rinv-mult G X (y , x) = pr₁ (ri (y , x)) , x
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G {pr₁ X}

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    ri : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    ri = pr₁ (pr₁ e)

torsor-linv-mult G X (y , x) = (pr₁ (li (y , x))) , x
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G {pr₁ X}

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    li : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    li = pr₁ (pr₂ e)

torsor-rinv-mult-is-right-inverse : (G : Group 𝓤) (X : Tors G) → 
                                    (mult G {pr₁ X}) ∘ (torsor-rinv-mult G X) ∼ id
torsor-rinv-mult-is-right-inverse G X (y , x) =  q ⁻¹
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G {pr₁ X}
    r : ⟨ G ⟩ → ⟨ pr₁ X ⟩
    r = right-mult G {pr₁ X} x

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    ri : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    ri = pr₁ (pr₁ e)

    e-ri : m ∘ ri ∼ id
    e-ri = pr₂ (pr₁ e)

    u : ⟨ pr₁ X ⟩ → ⟨ G ⟩
    u y = pr₁ (ri (y , x))

    p : pr₂ ( ri (y , x) ) ≡ x
    p = ap pr₂ (e-ri (y , x))

    q : y , x ≡ r (u y) , x
    q = y , x                      ≡⟨ e-ri (y , x) ⁻¹ ⟩
        m (ri (y , x))             ≡⟨ ap m refl ⟩
        m (u y , pr₂ (ri (y , x))) ≡⟨ ap (λ v → m (u y , v)) p ⟩
        m (u y , x)                ≡⟨ refl ⟩
        r (u y) , x ∎


torsor-linv-mult-is-left-inverse : (G : Group 𝓤) (X : Tors G) → 
                                   (torsor-linv-mult G X) ∘ (mult G {pr₁ X}) ∼ id
torsor-linv-mult-is-left-inverse G X (g , x) = q ⁻¹
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G {pr₁ X}
    r : ⟨ G ⟩ → ⟨ pr₁ X ⟩
    r = right-mult G {pr₁ X} x

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    li : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    li = pr₁ (pr₂ e)

    li-e : li ∘ m ∼ id
    li-e = pr₂ (pr₂ e)

    v : ⟨ pr₁ X ⟩ → ⟨ G ⟩
    v y = pr₁ (li (y , x))

    p : pr₂ (li (r g , x)) ≡ x
    p = ap pr₂ (li-e (g , x))

    q : g , x ≡ v (r g) , x
    q = g , x                        ≡⟨ li-e (g , x) ⁻¹ ⟩
        li (m (g , x))               ≡⟨ ap li (refl) ⟩
        li (r g , x)                 ≡⟨ refl ⟩
        v (r g) , pr₂ (li (r g , x)) ≡⟨ ap (λ z → v (r g) , z) p ⟩
        v (r g) , x ∎

\end{code}

A consequence of axioms is that for two points x y of a G-torsor there
is a unique g ∈ G bringing x to y.

\begin{code}

torsor-quotient-map : {G : Group 𝓤} (X : Tors G) (y x : ⟨ pr₁ X ⟩) → 
                      ∃! g ꞉ ⟨ G ⟩ , action-op G (pr₁ X) g x ≡ y
torsor-quotient-map {G = G} X y x = (g , ap pr₁ u) ,
               λ { (h , p) → to-Σ-≡ (ap pr₁ (ii h p) , carrier-is-set G (pr₁ X) _ _)}
    where
      gx : ⟨ G ⟩ × ⟨ pr₁ X ⟩
      gx = torsor-rinv-mult G X (y , x)

      g : ⟨ G ⟩
      g = pr₁ gx

      u : mult G {pr₁ X} gx ≡ y , x
      u = torsor-rinv-mult-is-right-inverse G X (y , x)

      m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
      m = mult G {pr₁ X}

      i : (h : ⟨ G ⟩) (p : action-op G (pr₁ X) h x ≡ y) → 
          m (g , x) ≡ m (h , x)
      i h p = m (g , x)                   ≡⟨ to-×-≡ (ap pr₁ u) refl ⟩
              y , x                       ≡⟨ to-×-≡ (p ⁻¹) refl ⟩
              action-op G (pr₁ X) h x , x ≡⟨ refl ⟩
              m (h , x) ∎

      ii : (h : ⟨ G ⟩) (p : action-op G (pr₁ X) h x ≡ y) →
           g , x ≡ h , x
      ii h p = g , x                            ≡⟨ q ⁻¹ ⟩
               torsor-linv-mult G X (m (g , x)) ≡⟨ ap (torsor-linv-mult G X) (i h p) ⟩
               torsor-linv-mult G X (m (h , x)) ≡⟨ r ⟩
               h , x ∎
                 where
                   q = torsor-linv-mult-is-left-inverse G X (g , x)
                   r = torsor-linv-mult-is-left-inverse G X (h , x)

\end{code}
 

