--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu
Keri D'Angelo kd349@cornell.edu

July 2022
--------------------------------------------------------------------------------

TORSORS. Split off from GroupActions. 

\begin{code}

{-# OPTIONS --without-K --safe --auto-inline --exact-split #-}


open import MLTT.Spartan
open import UF.Base hiding (_≈_)
open import UF.Subsingletons
open import UF.Powerset
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.Embeddings
open import UF.Univalence
open import UF.Equiv-FunExt
open import UF.FunExt
open import UF.UA-FunExt
open import UF.Subsingletons-FunExt
open import UF.Retracts
open import UF.Classifiers
open import UF.PropTrunc

open import Groups.Groups renaming (_≅_ to _≣_)
open import Groups.Groups-Supplement
open import Groups.GroupActions

module Groups.Torsors
--       (ua : is-univalent 𝓤)
       (fe : funext 𝓤 𝓤)
       (pt : propositional-truncations-exist)
     where

\end{code}


A G-torsor is a G-Set with nonempty underlying carrier and such that for
any x : X the right-multiplication map λ g → g · x is an equivalence.

\begin{code}

-- fe : funext 𝓤 𝓤
-- fe = univalence-gives-funext ua

open PropositionalTruncation pt

is-torsor : (G : Group 𝓤) (𝕏 : G Sets) → 𝓤  ̇
is-torsor G (X , a) = ∥ X ∥ ×
                    ((x : X) → is-equiv (right-mult G (X , a) x))

is-torsor-is-prop : (G : Group 𝓤) (𝕏 : G Sets) →
                    is-prop (is-torsor G 𝕏)
is-torsor-is-prop G 𝕏 = ×-is-prop ∥∥-is-prop
                          (Π-is-prop fe
                             (λ x → being-equiv-is-prop'' fe (right-mult G 𝕏 x)))

\end{code}

Alternative formulation: the "shear" map
(g , x) → (g · x , x) is an equivalence.

Those two formulations are equivalent (both being props).

\begin{code}
is-torsor₁ : (G : Group 𝓤) (𝕏 : G Sets) → 𝓤 ̇
is-torsor₁ G 𝕏 = ∥ ⟨ 𝕏 ⟩ ∥ × is-equiv (mult G 𝕏)

is-torsor₁-is-prop : (G : Group 𝓤) (𝕏 : G Sets) →
                     is-prop (is-torsor₁ G 𝕏)
is-torsor₁-is-prop G 𝕏 = ×-is-prop (∥∥-is-prop)
                           (being-equiv-is-prop'' fe (mult G 𝕏))

torsor→torsor₁ : {G : Group 𝓤} (𝕏 : G Sets) →
                 is-torsor G 𝕏 → is-torsor₁ G 𝕏
torsor→torsor₁ {G = G } (X , a) (n , e) = n , ee
  where
    ee : is-equiv (mult G (X , a))
    ee = (u , ε) , v , η
      where
        u : X × X → ⟨ G ⟩ × X
        u ( y , x) = (pr₁ (pr₁ (e x)) y) , x

        ε : (mult G (X , a)) ∘ u ∼ id
        ε (y , x) = to-×-＝ (pr₂ (pr₁ (e x)) y) refl

        v : X × X → ⟨ G ⟩ × X
        v (y , x) = pr₁ (pr₂ (e x)) y , x

        η : v ∘ (mult G (X , a)) ∼ id
        η (g , x) = to-×-＝ (pr₂ (pr₂ (e x)) g) refl

torsor₁→torsor : {G : Group 𝓤} (𝕏 : G Sets) →
                 is-torsor₁ G 𝕏 → is-torsor G 𝕏
torsor₁→torsor {G = G} (X , a) (n , e) = n , ee
  where
    ee : (x : X) → is-equiv (right-mult G (X , a) x)
    ee x = (u , ε) , v , η
      where
        m : ⟨ G ⟩ × X → X × X
        m = mult G (X , a)
        r : ⟨ G ⟩ → X
        r = right-mult G (X , a) x

        ri li : X × X → ⟨ G ⟩ × X
        ri = pr₁ (pr₁ e)
        li = pr₁ (pr₂ e)

        e-ri : m ∘ ri ∼ id
        e-ri = pr₂ (pr₁ e)

        li-e : li ∘ m ∼ id
        li-e = pr₂ (pr₂ e)

        γ : (g : ⟨ G ⟩) → m (g , x) ＝ r g , x
        γ g = refl

        u : X → ⟨ G ⟩
        u y = pr₁ (ri (y , x))

        ε : r ∘ u ∼ id
        ε y = ap pr₁ q ⁻¹
          where
            p : pr₂ ( ri (y , x) ) ＝ x
            p = ap pr₂ (e-ri (y , x))

            q : y , x ＝ r (u y) , x
            q = y , x                      ＝⟨ e-ri (y , x) ⁻¹ ⟩
                m (ri (y , x))             ＝⟨ ap m refl ⟩
                m (u y , pr₂ (ri (y , x))) ＝⟨ ap (λ v → m (u y , v)) p ⟩
                m (u y , x)                ＝⟨ γ (u y) ⟩
                r (u y) , x ∎

        v : X → ⟨ G ⟩
        v y = pr₁ (li (y , x))

        η : v ∘ r ∼ id
        η g = ap pr₁ q ⁻¹
          where
            p : pr₂ (li (r g , x)) ＝ x
            p = ap pr₂ (li-e (g , x))

            q : g , x ＝ v (r g) , x
            q = g , x                        ＝⟨ li-e (g , x) ⁻¹ ⟩
                li (m (g , x))               ＝⟨ ap li (γ g) ⟩
                li (r g , x)                 ＝⟨ refl ⟩
                v (r g) , pr₂ (li (r g , x)) ＝⟨ ap (λ z → v (r g) , z) p ⟩
                v (r g) , x ∎
\end{code}

-- The type of G-Torsors.

\begin{code} 

TORS Tors Torsor : (G : Group 𝓤) → (𝓤 ⁺) ̇
TORS G = Σ 𝕏 ꞉ Action G , is-torsor G 𝕏
Tors = TORS
Torsor = TORS

TORS' Tors' Torsor' : (G : Group 𝓤) → (𝓤 ⁺) ̇
TORS' G = Σ X ꞉ 𝓤 ̇ , Σ a ꞉ Action-structure G X , is-torsor G (X , a)
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

torsor-carrier-prop : {G : Group 𝓤} (X : Tors G) → ∥ (pr₁ (pr₁ X)) ∥
torsor-carrier-prop {G} X = pr₁ (torsor-prop {G} X)

torsor-nonempty : {G : Group 𝓤} (X : Tors G) → is-nonempty (pr₁ (pr₁ X))
torsor-nonempty {G} X = inhabited-is-nonempty (torsor-carrier-prop {G} X)

torsor-splitting : {G : Group 𝓤} (X : Tors G) → 
                   ((x : ⟨ pr₁ X ⟩) → is-equiv (right-mult G (pr₁ X) x))
torsor-splitting {G}  X = pr₂ (torsor-prop {G} X) 

torsor-splitting₁ : {G : Group 𝓤} (X : Tors G) →
                    is-equiv (mult G (pr₁ X))
torsor-splitting₁ {G = G} X = pr₂ (torsor→torsor₁ {G = G} (pr₁ X) (pr₂ X))

torsor-to-equiv : {G : Group 𝓤} (X : Tors G) →
                  (x : torsor-carrier {G = G} X) → ⟨ G ⟩ ≃ (torsor-carrier {G = G} X)
torsor-to-equiv {G = G} X x = (right-mult G (pr₁ X) x) , torsor-splitting {G = G} X x

\end{code}

The equivalence G × X → X × X is the counterpart to the classical fact
that the "shear" map G × X → X × X given by (g , x) ↦ (g · x , x) is
an isomorphism. In classical geometry this implies that the inverse
also has x as its second component. In other words, pr₂ = x.

Not so here, as highligheted by the convoluted proof above where an
explicit proof that pr₂ ( inverse (mult) (y , x)) ＝ x was needed.  We
codify this fact, as it will be useful elsewhere.

\begin{code}

torsor-rinv-mult torsor-linv-mult : (G : Group 𝓤) (X : Tors G) →
                                    (⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩)
torsor-rinv-mult G X (y , x) = pr₁ (ri (y , x)) , x
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G (pr₁ X)

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    ri : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    ri = pr₁ (pr₁ e)

torsor-linv-mult G X (y , x) = (pr₁ (li (y , x))) , x
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G (pr₁ X)

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    li : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    li = pr₁ (pr₂ e)

torsor-rinv-mult-is-right-inverse : (G : Group 𝓤) (X : Tors G) → 
                                    (mult G (pr₁ X)) ∘ (torsor-rinv-mult G X) ∼ id
torsor-rinv-mult-is-right-inverse G X (y , x) =  q ⁻¹
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G (pr₁ X)
    r : ⟨ G ⟩ → ⟨ pr₁ X ⟩
    r = right-mult G (pr₁ X) x

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    ri : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    ri = pr₁ (pr₁ e)

    e-ri : m ∘ ri ∼ id
    e-ri = pr₂ (pr₁ e)

    u : ⟨ pr₁ X ⟩ → ⟨ G ⟩
    u y = pr₁ (ri (y , x))

    p : pr₂ ( ri (y , x) ) ＝ x
    p = ap pr₂ (e-ri (y , x))

    q : y , x ＝ r (u y) , x
    q = y , x                      ＝⟨ e-ri (y , x) ⁻¹ ⟩
        m (ri (y , x))             ＝⟨ ap m refl ⟩
        m (u y , pr₂ (ri (y , x))) ＝⟨ ap (λ v → m (u y , v)) p ⟩
        m (u y , x)                ＝⟨ refl ⟩
        r (u y) , x ∎


torsor-linv-mult-is-left-inverse : (G : Group 𝓤) (X : Tors G) → 
                                   (torsor-linv-mult G X) ∘ (mult G (pr₁ X)) ∼ id
torsor-linv-mult-is-left-inverse G X (g , x) = q ⁻¹
  where
    m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
    m = mult G (pr₁ X)
    r : ⟨ G ⟩ → ⟨ pr₁ X ⟩
    r = right-mult G (pr₁ X) x

    e : is-equiv m
    e = torsor-splitting₁ {G = G} X

    li : ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩ → ⟨ G ⟩ × ⟨ pr₁ X ⟩
    li = pr₁ (pr₂ e)

    li-e : li ∘ m ∼ id
    li-e = pr₂ (pr₂ e)

    v : ⟨ pr₁ X ⟩ → ⟨ G ⟩
    v y = pr₁ (li (y , x))

    p : pr₂ (li (r g , x)) ＝ x
    p = ap pr₂ (li-e (g , x))

    q : g , x ＝ v (r g) , x
    q = g , x                        ＝⟨ li-e (g , x) ⁻¹ ⟩
        li (m (g , x))               ＝⟨ ap li (refl) ⟩
        li (r g , x)                 ＝⟨ refl ⟩
        v (r g) , pr₂ (li (r g , x)) ＝⟨ ap (λ z → v (r g) , z) p ⟩
        v (r g) , x ∎

\end{code}

If G is abelian, the underlying action is an equivariant map with
underlying weak equivalence, i.e. an ActionIso.

\begin{code}

left-mult-gives-ActionIso : (G : Group 𝓤) (i : is-abelian G) (X : Tors G) →
                      (g : ⟨ G ⟩) → Action-Iso G (pr₁ X) (pr₁ X)
left-mult-gives-ActionIso G i X g = (action-to-Aut G (pr₁ X) g) ,
                                      (λ a x → (
                                           g · (a · x)     ＝⟨ (action-assoc G 𝕏 g a x) ⁻¹ ⟩
                                           (g ·⟨ G ⟩ a) · x ＝⟨ ap (_· x) (i g a) ⟩
                                           (a ·⟨ G ⟩ g) · x ＝⟨ action-assoc G 𝕏 a g x ⟩
                                            a · (g · x) ∎ ))
  where
    𝕏 : Action G
    𝕏 = pr₁ X

    _·_ : ⟨ G ⟩ → ⟨ 𝕏 ⟩ → ⟨ 𝕏 ⟩
    _·_ = action-op G 𝕏

\end{code}

 
Forgetting the torsor axiom is an inclusion into the type of actions.

\begin{code}

underlying-action-is-embedding : (G : Group 𝓤) → is-embedding (underlying-action {G})
underlying-action-is-embedding G = pr₁-is-embedding (λ 𝕏 → is-torsor-is-prop G 𝕏)

underlying-action-injectivity :  (G : Group 𝓤) (X Y : Tors G) →
                                 (X ＝ Y) ≃ (underlying-action {G} X ＝ underlying-action  {G} Y)
underlying-action-injectivity G X Y = ≃-sym
                              (embedding-criterion-converse
                                (underlying-action {G = G})
                                (underlying-action-is-embedding G) X Y)

underlying-action-injectivity' : {G : Group 𝓤} {X Y : Tors G} →
                                 (X ＝ Y) ≃ (underlying-action {G} X ＝ underlying-action {G} Y)
underlying-action-injectivity' {G} {X} {Y} = ≃-sym
                              (embedding-criterion-converse
                                (underlying-action {G = G})
                                (underlying-action-is-embedding G) X Y)


underlying-action-injectivity-comp : {G : Group 𝓤} {X Y : Tors G} (p : X ＝ Y) →
                                     pr₁ (underlying-action-injectivity G X Y) p ＝ 
                                       ap (underlying-action {G})  p
underlying-action-injectivity-comp p = refl

\end{code}

For two points x y of a G-torsor there is a unique g ∈ G bringing x to
y. This is the "quotient map" of the G-torsor. Note that in the proof
below we need both "inverses" of the shear map (see above).

\begin{code}

torsor-division : (G : Group 𝓤) (X : Tors G) (y x : ⟨ pr₁ X ⟩) → 
                      ∃! g ꞉ ⟨ G ⟩ , action-op G (pr₁ X) g x ＝ y
torsor-division G X y x = (g , ap pr₁ u) ,
               λ { (h , p) → to-Σ-＝ (ap pr₁ (ii h p) , carrier-is-set G (pr₁ X) _ _)}
    where
      gx : ⟨ G ⟩ × ⟨ pr₁ X ⟩
      gx = torsor-rinv-mult G X (y , x)

      g : ⟨ G ⟩
      g = pr₁ gx

      u : mult G (pr₁ X) gx ＝ y , x
      u = torsor-rinv-mult-is-right-inverse G X (y , x)

      m : ⟨ G ⟩ × ⟨ pr₁ X ⟩ → ⟨ pr₁ X ⟩ × ⟨ pr₁ X ⟩
      m = mult G (pr₁ X)

      i : (h : ⟨ G ⟩) (p : action-op G (pr₁ X) h x ＝ y) → 
          m (g , x) ＝ m (h , x)
      i h p = m (g , x)                   ＝⟨ to-×-＝ (ap pr₁ u) refl ⟩
              y , x                       ＝⟨ to-×-＝ (p ⁻¹) refl ⟩
              action-op G (pr₁ X) h x , x ＝⟨ refl ⟩
              m (h , x) ∎

      ii : (h : ⟨ G ⟩) (p : action-op G (pr₁ X) h x ＝ y) →
           g , x ＝ h , x
      ii h p = g , x                            ＝⟨ q ⁻¹ ⟩
               torsor-linv-mult G X (m (g , x)) ＝⟨ ap (torsor-linv-mult G X) (i h p) ⟩
               torsor-linv-mult G X (m (h , x)) ＝⟨ r ⟩
               h , x ∎
                 where
                   q = torsor-linv-mult-is-left-inverse G X (g , x)
                   r = torsor-linv-mult-is-left-inverse G X (h , x)

torsor-division-map : {G : Group 𝓤} {X : Tors G} →
                      (y x : ⟨ pr₁ X ⟩) → ⟨ G ⟩
torsor-division-map {G = G} {X} y x = pr₁ (pr₁ (torsor-division G X y x ))

-- type as \ldiv
syntax torsor-division-map y x = y ∕ x
\end{code}


A map of torsors in just an equivariant map, that is, a morphism of
the underlying actions.

One of the fundamental facts about torsors is that a map f : X → Y of
G-torsors is necessarily an isomorphism. In our case, an equivalence.

\begin{code}

torsor-map-is-equiv : {G : Group 𝓤} {X Y : Tors G}
                      ((f , is) : Action-Map G (pr₁ X) (pr₁ Y)) →
                      is-equiv f
torsor-map-is-equiv {G} {𝕏 , tx} {𝕐 , ty} (f , is) = ∥∥-rec (being-equiv-is-prop'' fe f) γ (pr₁ tx)
  where
    X Y : 𝓤 ̇
    X = ⟨ 𝕏 ⟩
    Y = ⟨ 𝕐 ⟩
    _·_ : ⟨ G ⟩ → X → X
    _·_ = action-op G 𝕏
    _*_ : ⟨ G ⟩ → Y → Y
    _*_ = action-op G 𝕐

    module _ (x₀ : X) where
       rx : ⟨ G ⟩ → X
       rx = right-mult G 𝕏 x₀
       ry : ⟨ G ⟩ → Y
       ry = right-mult G 𝕐 (f x₀)

       h : f ∘ rx ∼ ry ∘ id
       h g = f (rx g)   ＝⟨ refl ⟩
             f (g · x₀) ＝⟨ is g x₀ ⟩
             g * (f x₀) ＝⟨ refl ⟩
             ry g ∎

       i : is-equiv (f ∘ rx)
       i = equiv-closed-under-∼ ry (f ∘ rx) (pr₂ ty (f x₀)) h

       γ : is-equiv f
       γ = ≃-2-out-of-3-right (pr₂ tx x₀) i

torsor-map-to-Action-Iso : {G : Group 𝓤} {(𝕏 , _) (𝕐 , _) : Tors G}
                           (f : Action-Map G 𝕏 𝕐) → Action-Iso G 𝕏 𝕐
torsor-map-to-Action-Iso {G} {X} {Y} f = ((pr₁ f) , (torsor-map-is-equiv {G} {X} {Y} f)) , (pr₂ f)

Hom : {G : Group 𝓤} → Tors G → Tors G → 𝓤 ̇
Hom {G} X Y = Action-Map G (pr₁ X) (pr₁ Y)

trivial-torsor : (G : Group 𝓤) → Tors G
trivial-torsor G = (⟨ G ⟩ , ((multiplication G) , ((group-is-set G) , ((assoc G) , (unit-left G))))) ,
                   (∣ unit G ∣ , λ x → qinvs-are-equivs  (λ a → a ·⟨ G ⟩ x)
                                       ((λ a → a ·⟨ G ⟩ (inv G x)) ,
                                     ((λ a → ((a ·⟨ G ⟩ x) ·⟨ G ⟩ (inv G x) ＝⟨ assoc G _ _ _ ⟩
                                              a ·⟨ G ⟩ (x ·⟨ G ⟩ (inv G x)) ＝⟨ ap (λ v → a ·⟨ G ⟩ v) (inv-right G x) ⟩
                                              a ·⟨ G ⟩ (unit G)            ＝⟨ unit-right G a ⟩
                                              a ∎)) ,
                                      (λ a → ((a ·⟨ G ⟩ (inv G x)) ·⟨ G ⟩ x ＝⟨ assoc G _ _ _ ⟩
                                              a ·⟨ G ⟩ ((inv G x) ·⟨ G ⟩ x) ＝⟨ ap (λ v → a ·⟨ G ⟩ v) (inv-left G x) ⟩
                                              a ·⟨ G ⟩ (unit G)            ＝⟨ unit-right G a ⟩
                                              a ∎)))))
\end{code}

A point x in a torsor X determines a map trivial-torsor G → X

\begin{code}

univ-function : {G : Group 𝓤} (X : Tors G) (x : ⟨ pr₁ X ⟩) →
                ⟨ pr₁ (trivial-torsor G) ⟩ → ⟨ pr₁ X ⟩
univ-function {G} X x = right-mult G (pr₁ X) x

univ-function-equivariant : {G : Group 𝓤} (X : Tors G) (x : ⟨ pr₁ X ⟩) →
                            is-equivariant G  (pr₁ (trivial-torsor G)) (pr₁ X) (univ-function {G} X x)
univ-function-equivariant {G} X x = {!!}

\end{code}
