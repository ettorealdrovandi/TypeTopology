--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu

October 2023
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --without-K --safe  --exact-split #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Groupoids
open import PathSequences.Type
open import PathSequences.Reasoning
open import PathSequences.Rotations
open import 2Groups.Type

\end{code}

V. Redundant Axioms
===================

We implement the arguments in

1. Joyal, Street: Braided Tensor Categories.
2. Mac Lane: Categories for the Working Mathematician.

to show that `⊗-assoc-neutral-l`, `⊗-assoc-neutral-r`,
`left-right-neutral-compatibility` follow from the rest. 

Below we assume the product structure is in the most general form,
that is, we do not assume the product on the identity types, the
interchange and preservation of refl be induced from 
(_●_ : ⊗-structure X).

\begin{code}

module 2Groups.RedundantAxiomsPathSeq
         (X : 𝓤 ̇)
         (_●_ : ⊗-structure X)
         (_✶_ : ⊗-structure-Id X _●_)
         (𝓘 : ⊗-structure-Id-interchange X _●_ _✶_)
         (𝓲𝓭 : ⊗-preserves-id X _●_ _✶_)
         (α : associative _●_)
         (π : ⊗-assoc-pentagon X _●_ _✶_ α)
         (φₐₛ : ⊗-assoc-compatible-with-＝ X _●_ _✶_ α)
         (e : X)
         (𝓵 : left-neutral e _●_)
         (𝓻 : right-neutral e _●_)
         (φᵢ : ⊗-assoc-neutral X _●_ _✶_ α e 𝓵 𝓻)
         (φₗ : left-neutral-compatible-with-＝ X _●_ _✶_ e 𝓵 𝓻)
         (φᵣ : right-neutral-compatible-with-＝ X _●_ _✶_ e 𝓵 𝓻)
           where
\end{code}


⊗-assoc-neutral-r is a consequence of ⊗-assoc-neutral and the
naturality axioms. We prove the commutativity of the following two
diagrams:

% https://q.uiver.app/?q=WzAsNyxbMCwwLCIoKHh5KWUpZSJdLFsyLDAsIih4KHllKSllIl0sWzQsMCwieCgoeWUpZSkiXSxbNCwyLCJ4KHkoZWUpKSJdLFswLDIsIih4eSkoZWUpIl0sWzEsMSwiKHh5KWUiXSxbMywxLCJ4KHllKSJdLFswLDEsInAiXSxbMSwyLCJxIl0sWzIsMywiciJdLFswLDQsInUiLDJdLFs0LDMsInYiLDJdLFswLDUsInMnJyIsMl0sWzUsNiwicSciLDIseyJsYWJlbF9wb3NpdGlvbiI6NjB9XSxbMSw1LCJ0JyJdLFsyLDYsInQiXSxbMyw2LCJzIiwyXSxbNCw1LCJzJyIsMl1d
\[\begin{tikzcd}
	{((xy)e)e} && {(x(ye))e} && {x((ye)e)} \\
	& {(xy)e} && {x(ye)} \\
	{(xy)(ee)} &&&& {x(y(ee))}
	\arrow["p", from=1-1, to=1-3]
	\arrow["q", from=1-3, to=1-5]
	\arrow["r", from=1-5, to=3-5]
	\arrow["u"', from=1-1, to=3-1]
	\arrow["v"', from=3-1, to=3-5]
	\arrow["{s''}"', from=1-1, to=2-2]
	\arrow["{q'}"'{pos=0.6}, from=2-2, to=2-4]
	\arrow["{t'}", from=1-3, to=2-2]
	\arrow["t", from=1-5, to=2-4]
	\arrow["s"', from=3-5, to=2-4]
	\arrow["{s'}"', from=3-1, to=2-2]
\end{tikzcd}\]

% https://q.uiver.app/?q=WzAsOCxbMiwyLCIoeHkpZSIsWzI0NCw4Niw2MCwxXV0sWzQsMiwieCh5ZSkiLFsyNDQsODYsNjAsMV1dLFswLDBdLFs2LDBdLFsxLDEsIigoeHkpZSllIl0sWzUsMSwiKHgoeWUpKWUiXSxbMyw1LCIoeHkpZSJdLFszLDMsInh5IixbMjQ0LDg2LDYwLDFdXSxbMCwxLCJcXGFscGhhIiwwLHsiY29sb3VyIjpbMjQ0LDg2LDYwXX0sWzI0NCw4Niw2MCwxXV0sWzQsNSwicCJdLFs0LDYsInMnJyIsMix7ImN1cnZlIjoyfV0sWzUsNiwidCciLDAseyJjdXJ2ZSI6LTJ9XSxbNSwxLCJyX3t4KHllKX0iLDIseyJsYWJlbF9wb3NpdGlvbiI6NzB9XSxbNCwwLCJyX3soeHkpZX0iLDAseyJsYWJlbF9wb3NpdGlvbiI6NzB9XSxbMCw3LCJyX3t4eX0iLDIseyJsYWJlbF9wb3NpdGlvbiI6MzAsImNvbG91ciI6WzI0NCw4Niw2MF19LFsyNDQsODYsNjAsMV1dLFsxLDcsInggcl95IiwwLHsibGFiZWxfcG9zaXRpb24iOjIwLCJjb2xvdXIiOlsyNDQsODYsNjBdfSxbMjQ0LDg2LDYwLDFdXSxbNiw3LCJyX3t4eX0iLDFdXQ==
\[\begin{tikzcd}
	{} &&&&&& {} \\
	& {((xy)e)e} &&&& {(x(ye))e} \\
	&& \textcolor{rgb,255:red,77;green,65;blue,241}{(xy)e} && \textcolor{rgb,255:red,77;green,65;blue,241}{x(ye)} \\
	&&& \textcolor{rgb,255:red,77;green,65;blue,241}{xy} \\
	\\
	&&& {(xy)e}
	\arrow["\alpha", color={rgb,255:red,77;green,65;blue,241}, from=3-3, to=3-5]
	\arrow["p", from=2-2, to=2-6]
	\arrow["{s''}"', curve={height=12pt}, from=2-2, to=6-4]
	\arrow["{t'}", curve={height=-12pt}, from=2-6, to=6-4]
	\arrow["{r_{x(ye)}}"'{pos=0.7}, from=2-6, to=3-5]
	\arrow["{r_{(xy)e}}"{pos=0.7}, from=2-2, to=3-3]
	\arrow["{r_{xy}}"'{pos=0.3}, color={rgb,255:red,77;green,65;blue,241}, from=3-3, to=4-4]
	\arrow["{x r_y}"{pos=0.2}, color={rgb,255:red,77;green,65;blue,241}, from=3-5, to=4-4]
	\arrow["{r_{xy}}"{description}, from=6-4, to=4-4]
\end{tikzcd}\]

\begin{code}

  have-⊗-assoc-neutral-r : ⊗-assoc-neutral-r X _●_ _✶_ α e 𝓵 𝓻
  have-⊗-assoc-neutral-r {x} {y} = ＝ₛ-out iv
    where
      p : ((x ● y) ● e) ● e ＝ (x ● (y ● e)) ● e
      p = (α x y e) ✶ refl
      q : (x ● (y ● e)) ● e ＝ x ● ((y ● e) ● e)
      q = α x (y ● e) e
      q' : (x ● y) ● e ＝ x ● (y ● e)
      q' = α x y e
      r : x ● ((y ● e) ● e) ＝ x ● (y ● (e ● e))
      r = refl ✶ (α y e e)
      s : x ● (y ● (e ● e)) ＝ x ● (y ● e)
      s = refl ✶ (refl ✶ 𝓵 e)
      s' : (x ● y) ● (e ● e) ＝ (x ● y) ● e
      s' = refl ✶ (𝓵 e)
      s₁' : (x ● y) ● (e ● e) ＝ (x ● y) ● e
      s₁' = (refl ✶ refl) ✶ (𝓵 e)
      s'' : ((x ● y) ● e) ● e ＝ (x ● y) ● e
      s'' = 𝓻 (x ● y) ✶ refl
      t : x ● ((y ● e) ● e) ＝ x ● (y ● e)
      t = refl ✶ ((𝓻 y) ✶ refl)
      t' : (x ● (y ● e)) ● e ＝ (x ● y) ● e
      t' = ((refl ✶ 𝓻 y)) ✶ refl
      u : ((x ● y) ● e) ● e ＝ (x ● y) ● (e ● e)
      u = α (x ● y) e e
      v : (x ● y) ● (e ● e) ＝ x ● (y ● (e ● e))
      v = α x y (e ● e)

      i : p ◃∙ q ◃∙ r ◃∙ s ◃∎ ＝ₛ p ◃∙ t' ◃∙ q' ◃∎
      i = p ◃∙ q ◃∙ r ◃∙ s ◃∎                            ＝↓⟨ 2 & 2 & 𝓘 refl refl (α y e e) (refl ✶ 𝓵 e) ⟩
          p ◃∙ q ◃∙ (refl ✶ (α y e e ∙ (refl ✶ 𝓵 e))) ◃∎ ＝↓⟨ 2 & 1 & ap (refl ✶_) φᵢ ⟩
          p ◃∙ q ◃∙ t ◃∎                                 ＝ₛ⟨ 1 & 2 & ＝ₛ-in (φₐₛ refl (𝓻 y) refl) ⟩ 
          p ◃∙ t' ◃∙ q' ◃∎                                ∎ₛ

      ii : p ◃∙ q ◃∙ r ◃∙ s ◃∎ ＝ₛ s'' ◃∙ q' ◃∎
      ii = p ◃∙ q ◃∙ r ◃∙ s ◃∎  ＝ₛ⟨ 0 & 3 & I ⟩
           u ◃∙ v ◃∙ s ◃∎       ＝ₛ⟨ 1 & 3 & ＝ₛ-in (φₐₛ refl refl (𝓵 e)) ⟩
           u ◃∙ s₁' ◃∙ q' ◃∎    ＝↓⟨ 1 & 1 & (ap (_✶ (𝓵 e)) 𝓲𝓭) ⟩
           u ◃∙ s' ◃∙ q' ◃∎     ＝ₛ⟨ 0 & 2 & II ⟩
           s'' ◃∙ q' ◃∎         ∎ₛ
             where
               I : p ◃∙ q ◃∙ r ◃∎ ＝ₛ u ◃∙ v ◃∎
               I = ＝ₛ-in π
               II : u ◃∙ s' ◃∎ ＝ₛ s'' ◃∎
               II = ＝ₛ-in φᵢ

      iii : p ◃∙ t' ◃∎ ＝ₛ s'' ◃∎
      iii = p ◃∙ t' ◃∎                     ＝ₛ⟨ 2 & 0 & ＝ₛ-in (right-inverse q') ⟩
            p ◃∙ t' ◃∙ q' ◃∙ (q' ⁻¹) ◃∎    ＝ₛ⟨ 0 & 3 & (i ⁻¹ₛ) ∙ₛ ii ⟩
            s'' ◃∙ q' ◃∙  (q' ⁻¹) ◃∎       ＝ₛ⟨ 1 & 2 & ＝ₛ-in ((right-inverse q') ⁻¹) ⟩
            s'' ◃∎     ∎ₛ

      iv : α x y e ◃∙ ((𝓻𝓮𝒻𝓵 x) ✶ (𝓻 y)) ◃∎ ＝ₛ 𝓻 (x ● y) ◃∎
      iv = α x y e ◃∙ ((𝓻𝓮𝒻𝓵 x) ✶ (𝓻 y)) ◃∎
             ＝ₛ⟨ 0 & 0 & I ⟩
           (𝓻 ((x ● y) ● e) ⁻¹) ◃∙ 𝓻 ((x ● y) ● e) ◃∙ α x y e ◃∙ ((𝓻𝓮𝒻𝓵 x) ✶ (𝓻 y)) ◃∎
             ＝ₛ⟨ 1 & 2 & II ⟩
           (𝓻 ((x ● y) ● e) ⁻¹) ◃∙ p ◃∙ 𝓻 (x ● (y ● e)) ◃∙ ((𝓻𝓮𝒻𝓵 x) ✶ (𝓻 y)) ◃∎
             ＝ₛ⟨ 2 & 2 & ＝ₛ-in (φᵣ (refl ✶ (𝓻 y)) ⁻¹) ⟩
           (𝓻 ((x ● y) ● e) ⁻¹) ◃∙ p ◃∙ t' ◃∙ 𝓻 (x ● y) ◃∎
             ＝ₛ⟨ 1 & 2 & iii ⟩
           (𝓻 ((x ● y) ● e) ⁻¹) ◃∙ s'' ◃∙ 𝓻 (x ● y) ◃∎
             ＝ₛ⟨ 1 & 2 & ＝ₛ-in (φᵣ (𝓻 (x ● y))) ⟩
           (𝓻 ((x ● y) ● e) ⁻¹) ◃∙ 𝓻 ((x ● y) ● e) ◃∙ 𝓻 (x ● y) ◃∎
             ＝ₛ⟨ 0 & 2 & I ⁻¹ₛ ⟩ 
           𝓻 (x ● y) ◃∎ ∎ₛ
             where
               I : [] ＝ₛ (𝓻 ((x ● y) ● e) ⁻¹) ◃∙ 𝓻 ((x ● y) ● e) ◃∎
               I = ＝ₛ-in (left-inverse (𝓻 ((x ● y) ● e)) ⁻¹)
               II : 𝓻 ((x ● y) ● e) ◃∙ α x y e ◃∙ [] ＝ₛ p ◃∙ 𝓻 (x ● (y ● e)) ◃∙ []
               II = ＝ₛ-in (φᵣ (α x y e) ⁻¹)
\end{code}

This shows how to get ⊗-assoc-neutral-l from ⊗-assoc-neutral plus the
naturality axioms.

The two diagrams analyzed in the code below are:

% https://q.uiver.app/?q=WzAsNyxbMCwwLCIoKGUgZSl4KXkiXSxbNCwwLCIoZShleCkpeSJdLFsyLDEsIihleCl5Il0sWzIsMywiZSh4eSkiXSxbNCwyLCJlKChleCl5KSJdLFs0LDQsImUoZSh4eSkpIl0sWzAsNCwiKGVlKSh4eSkiXSxbMCwxLCJwIl0sWzEsMiwidCciLDFdLFsyLDMsInEnIl0sWzEsNCwicSJdLFs0LDMsInQiLDFdLFs0LDUsInIiXSxbNSwzLCJzIiwxXSxbNiw1LCJ2Il0sWzAsNiwidSIsMV0sWzAsMiwidyciLDFdLFs2LDMsInciLDFdLFsxMSwxMywiPyIsMSx7Im9mZnNldCI6LTIsInNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sImxldmVsIjoxLCJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJub25lIn0sImhlYWQiOnsibmFtZSI6Im5vbmUifX19XV0=
\[\begin{tikzcd}
	{((e e)x)y} &&&& {(e(ex))y} \\
	&& {(ex)y} \\
	&&&& {e((ex)y)} \\
	&& {e(xy)} \\
	{(ee)(xy)} &&&& {e(e(xy))}
	\arrow["p", from=1-1, to=1-5]
	\arrow["{t'}"{description}, from=1-5, to=2-3]
	\arrow["{q'}", from=2-3, to=4-3]
	\arrow["q", from=1-5, to=3-5]
	\arrow[""{name=0, anchor=center, inner sep=0}, "t"{description}, from=3-5, to=4-3]
	\arrow["r", from=3-5, to=5-5]
	\arrow[""{name=1, anchor=center, inner sep=0}, "s"{description}, from=5-5, to=4-3]
	\arrow["v", from=5-1, to=5-5]
	\arrow["u"{description}, from=1-1, to=5-1]
	\arrow["{w'}"{description}, from=1-1, to=2-3]
	\arrow["w"{description}, from=5-1, to=4-3]
	\arrow["{?}"{description}, shift left=2, draw=none, from=0, to=1]
\end{tikzcd}\]

and:

% https://q.uiver.app/?q=WzAsNixbMCwyLCJlKHh5KSJdLFsxLDIsInh5Il0sWzIsMSwiKGV4KXkiXSxbMiwzLCJlKHh5KSJdLFszLDAsImUoKGV4KXkpIl0sWzMsNCwiZShlKHh5KSkiXSxbMCwxXSxbMiwxLCJ0XzEiLDJdLFsyLDMsInJfMSJdLFszLDEsInNfMSJdLFs0LDJdLFs0LDAsInQiLDEseyJjdXJ2ZSI6M31dLFs0LDUsInIiXSxbNSwzXSxbNSwwLCJzIiwxLHsiY3VydmUiOi0zfV1d
\[\begin{tikzcd}
	&&& {e((ex)y)} \\
	&& {(ex)y} \\
	{e(xy)} & xy \\
	&& {e(xy)} \\
	&&& {e(e(xy))}
	\arrow[from=3-1, to=3-2]
	\arrow["{t_1}"', from=2-3, to=3-2]
	\arrow["{r_1}", from=2-3, to=4-3]
	\arrow["{s_1}", from=4-3, to=3-2]
	\arrow[from=1-4, to=2-3]
	\arrow["t"{description}, curve={height=18pt}, from=1-4, to=3-1]
	\arrow["r", from=1-4, to=5-4]
	\arrow[from=5-4, to=4-3]
	\arrow["s"{description}, curve={height=-18pt}, from=5-4, to=3-1]
\end{tikzcd}\]

\begin{code}

  have-⊗-assoc-neutral-l : ⊗-assoc-neutral-l X _●_ _✶_ α e 𝓵 𝓻
  have-⊗-assoc-neutral-l {x} {y} = ＝ₛ-out vi
    where
      p : ((e ● e) ● x) ● y ＝ (e ● (e ● x)) ● y
      p = (α e e x) ✶ refl

      q : (e ● (e ● x)) ● y ＝ e ● ((e ● x) ● y)
      q = α e (e ● x) y

      q' : (e ● x) ● y ＝ e ● (x ● y)
      q' = α e x y

      r : e ● ((e ● x) ● y) ＝ e ● (e ● (x ● y))
      r = refl ✶ (α e x y)

      s : e ● (e ● (x ● y)) ＝ e ● (x ● y)
      s = refl ✶ 𝓵 (x ● y)

      t : e ● ((e ● x) ● y) ＝ e ● (x ● y)
      t = refl ✶ ((𝓵 x) ✶ refl)

      u : ((e ● e) ● x) ● y ＝ (e ● e) ● (x ● y)
      u = α (e ● e) x y

      v : (e ● e) ● (x ● y) ＝ e ● (e ● (x ● y))
      v = α e e (x ● y)

      w : (e ● e) ● (x ● y) ＝ e ● (x ● y)
      w = (𝓻 e) ✶ refl

      w'' : (e ● e) ● (x ● y) ＝ e ● (x ● y)
      w'' = (𝓻 e) ✶ (refl ✶ refl)

      w' : ((e ● e) ● x) ● y ＝ (e ● x) ● y
      w' = ((𝓻 e) ✶ refl) ✶ refl

      t' : (e ● (e ● x)) ● y ＝ (e ● x) ● y
      t' = (refl ✶ (𝓵 x)) ✶ refl

      i : p ◃∙ q ◃∙ t ◃∎ ＝ₛ w' ◃∙ q' ◃∎
      i = p ◃∙ q ◃∙ t ◃∎      ＝ₛ⟨ 1 & 2 & ＝ₛ-in (φₐₛ refl (𝓵 x) refl) ⟩
          p ◃∙ t' ◃∙ q' ◃∎    ＝↓⟨ 0 & 2 & 𝓘 (α e e x) (refl ✶ 𝓵 x) refl refl ⟩
          ((α e e x ∙ ((𝓻𝓮𝒻𝓵 e) ✶ 𝓵 x)) ✶ (𝓻𝓮𝒻𝓵 y)) ◃∙ q' ◃∎ ＝ₛ⟨ 0 & 1 & I ⟩
          w' ◃∙ q' ◃∎         ∎ₛ
            where
              I : ((α e e x ∙ ((𝓻𝓮𝒻𝓵 e) ✶ 𝓵 x)) ✶ (𝓻𝓮𝒻𝓵 y)) ◃∙ [] ＝ₛ w' ◃∙ []
              I = ＝ₛ-in (ap (_✶ 𝓻𝓮𝒻𝓵 y) φᵢ)

      ii : p ◃∙ q ◃∙ r ◃∙ s ◃∎ ＝ₛ w' ◃∙ q' ◃∎
      ii = p ◃∙ q ◃∙ r ◃∙ s ◃∎ ＝ₛ⟨ 0 & 3 & I ⟩
           u ◃∙ v ◃∙ s ◃∎      ＝ₛ⟨ 1 & 2 & ＝ₛ-in φᵢ ⟩
           u ◃∙ w ◃∎           ＝ₛ⟨ II ⟩
           w' ◃∙ q' ◃∎         ∎ₛ 
             where
               I : p ◃∙ q ◃∙ r ◃∙ [] ＝ₛ u ◃∙ v ◃∙ []
               I = ＝ₛ-in π
               II : u ◃∙ w ◃∎ ＝ₛ w' ◃∙ q' ◃∎
               II = (α (e ● e) x y) ◃∙ ((𝓻 e) ✶ refl) ◃∎
                       ＝ₛ⟨ 1 & 1 & ＝ₛ-in (ap ((𝓻 e) ✶_ ) 𝓲𝓭 ⁻¹) ⟩
                    (α (e ● e) x y) ◃∙ ((𝓻 e) ✶ (refl ✶ refl)) ◃∎
                       ＝ₛ⟨ ＝ₛ-in (φₐₛ (𝓻 e) refl refl) ⟩
                    (((𝓻 e) ✶ refl) ✶ refl) ◃∙ α e x y ◃∎
                        ∎ₛ

      iii : p ◃∙ q ◃∙ r ◃∙ s ◃∎ ＝ₛ p ◃∙ q ◃∙ t ◃∎
      iii = p ◃∙ q ◃∙ r ◃∙ s ◃∎ ＝ₛ⟨ ii ⟩
            w' ◃∙ q' ◃∎         ＝ₛ⟨ i ⁻¹ₛ ⟩
            p ◃∙ q ◃∙ t ◃∎      ∎ₛ


      iv : r ◃∙ s ◃∎ ＝ₛ t ◃∎
      iv = r ◃∙ s ◃∎ ＝ₛ⟨ pre-rotate-seq-in {p = p ◃∙ q ◃∎} iii ⟩
           (q ⁻¹) ◃∙ (p ⁻¹) ◃∙ p ◃∙ q ◃∙ t ◃∎
                     ＝ₛ⟨ 1 & 2 & I ⟩ 
           (q ⁻¹) ◃∙ q ◃∙ t ◃∎
                     ＝ₛ⟨ 0 & 2 & II ⟩
           t ◃∎      ∎ₛ
             where
               I : (p ⁻¹) ◃∙ p ◃∙ [] ＝ₛ []
               I = ＝ₛ-in (left-inverse p)
               II : (q ⁻¹) ◃∙ q ◃∙ [] ＝ₛ []
               II = ＝ₛ-in (left-inverse q)

      𝕧 : 𝓵 ((e ● x) ● y) ◃∙ α e x y ◃∙ 𝓵 (x ● y) ◃∎ ＝ₛ 𝓵 ((e ● x) ● y) ◃∙ ((𝓵 x) ✶ refl) ◃∎
      𝕧 = 𝓵 ((e ● x) ● y) ◃∙ α e x y ◃∙ 𝓵 (x ● y) ◃∎
            ＝ₛ⟨ 0 & 2 & I ⟩
          r ◃∙ 𝓵 (e ● (x ● y)) ◃∙ 𝓵 (x ● y) ◃∎
            ＝ₛ⟨ 1 & 2 & ＝ₛ-in (φₗ (𝓵 (x ● y)) ⁻¹) ⟩
          r ◃∙ s ◃∙ 𝓵 (x ● y) ◃∎
            ＝ₛ⟨ 0 & 2 & iv ⟩
          t ◃∙ 𝓵 (x ● y) ◃∎
            ＝ₛ⟨ 0 & 2 & ＝ₛ-in (φₗ (𝓵 x ✶ refl)) ⟩
          𝓵 ((e ● x) ● y) ◃∙ ((𝓵 x) ✶ refl) ◃∎
            ∎ₛ
            where
              I : 𝓵 ((e ● x) ● y) ◃∙ α e x y ◃∎ ＝ₛ r ◃∙ 𝓵 (e ● (x ● y)) ◃∎
              I = ＝ₛ-in (φₗ (α e x y) ⁻¹)

      vi : α e x y ◃∙ 𝓵 (x ● y) ◃∎ ＝ₛ ((𝓵 x) ✶ refl) ◃∎
      vi = α e x y ◃∙ 𝓵 (x ● y) ◃∎
             ＝ₛ⟨ pre-rotate-in 𝕧 ⟩
           (𝓵 ((e ● x) ● y) ⁻¹) ◃∙ 𝓵 ((e ● x) ● y) ◃∙ ((𝓵 x) ✶ refl) ◃∎
             ＝ₛ⟨ 0 & 2 & I ⟩ 
           ((𝓵 x) ✶ refl) ◃∎
             ∎ₛ
             where
               I : (𝓵 ((e ● x) ● y) ⁻¹) ◃∙ 𝓵 ((e ● x) ● y) ◃∙ [] ＝ₛ []
               I = ＝ₛ-in (left-inverse (𝓵 ((e ● x) ● y)))

\end{code}

Finally, the axiom establishing that 𝓵 e ＝ 𝓻 e is also a consequence
of the others.

\begin{code}

  have-left-right-neutral-compat : left-right-neutral-compatibility X _●_ _✶_ e 𝓵 𝓻
  have-left-right-neutral-compat = ＝ₛ-out (v ⁻¹ₛ)
    where
      i :  ((𝓻𝓮𝒻𝓵 e) ✶ 𝓵 e) ◃∙ 𝓵 e ◃∎ ＝ₛ 𝓵 (e ● e) ◃∙ 𝓵 e ◃∎
      i = ＝ₛ-in (φₗ (𝓵 e))

      ii : ((𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∙ 𝓵 e ◃∎ ＝ₛ ((𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∙ 𝓵 e ◃∎
      ii = ((𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∙ 𝓵 e ◃∎
                  ＝ₛ⟨  0 & 1 & I ⟩
           (α e e e) ◃∙ ((𝓻𝓮𝒻𝓵 e) ✶ (𝓵 e)) ◃∙ 𝓵 e ◃∎
               ＝ₛ⟨ 1 & 2 & i ⟩
           (α e e e) ◃∙ 𝓵 (e ● e) ◃∙ 𝓵 e ◃∎
                ＝ₛ⟨ 0 & 2 & II ⟩
           ((𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∙ 𝓵 e ◃∎
               ∎ₛ
               where
                 I : ((𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∎ ＝ₛ (α e e e) ◃∙ ((𝓻𝓮𝒻𝓵 e) ✶ (𝓵 e)) ◃∎
                 I = ＝ₛ-in (φᵢ ⁻¹)
                 II : (α e e e) ◃∙ 𝓵 (e ● e) ◃∎ ＝ₛ ((𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∎
                 II = ＝ₛ-in have-⊗-assoc-neutral-l

      iii : ((𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∎ ＝ₛ ((𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∎
      iii = ((𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∎
                ＝ₛ⟨ post-rotate-in ii ⟩
            ((𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∙ 𝓵 e ◃∙ (𝓵 e ⁻¹) ◃∎
                ＝ₛ⟨ 1 & 2 & ＝ₛ-in (right-inverse (𝓵 e) ⁻¹) ⟩ 
            ((𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∎
                ∎ₛ

      iv : 𝓻 (e ● e) ◃∙ (𝓻 e) ◃∎ ＝ₛ 𝓻 (e ● e) ◃∙ (𝓵 e) ◃∎
      iv = 𝓻 (e ● e) ◃∙ (𝓻 e) ◃∎
                ＝ₛ⟨ ＝ₛ-in (φᵣ (𝓻 e) ⁻¹) ⟩ 
           ((𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∙ (𝓻 e) ◃∎
                ＝ₛ⟨ 0 & 1 & iii ⟩
           ((𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e)) ◃∙ (𝓻 e) ◃∎
                ＝ₛ⟨ ＝ₛ-in (φᵣ (𝓵 e)) ⟩ 
           𝓻 (e ● e) ◃∙ (𝓵 e) ◃∎
                 ∎ₛ

      v : 𝓻 e ◃∎ ＝ₛ 𝓵 e ◃∎
      v = 𝓻 e ◃∎
            ＝ₛ⟨ pre-rotate-in iv ⟩
          (𝓻 (e ● e) ⁻¹) ◃∙ 𝓻 (e ● e) ◃∙ (𝓵 e) ◃∎
            ＝ₛ⟨ 0 & 2 & I ⟩
          𝓵 e ◃∎  ∎ₛ
            where
              I : (𝓻 (e ● e) ⁻¹) ◃∙ 𝓻 (e ● e) ◃∎ ＝ₛ []
              I = ＝ₛ-in (left-inverse (𝓻 (e ● e)))

\end{code}
