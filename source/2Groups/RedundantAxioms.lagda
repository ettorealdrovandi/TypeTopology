--------------------------------------------------------------------------------
Ettore Aldrovandi ealdrovandi@fsu.edu

October 2023
--------------------------------------------------------------------------------

\begin{code}

{-# OPTIONS --without-K --safe  --exact-split #-}

open import MLTT.Spartan
open import UF.Base
open import UF.Groupoids
open import 2Groups.Type
open import Groups.Type using (⟨_⟩)

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

module 2Groups.RedundantAxioms where

module _ (X : 𝓤 ̇)
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
 opaque
\end{code}

This shows how to get ⊗-assoc-neutral-l from ⊗-assoc-neutral plus the naturality axioms.

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
  have-⊗-assoc-neutral-l {x} {y} = l-4
    where
      p : ((e ● e) ● x) ● y ＝ (e ● (e ● x)) ● y
      p = (α e e x) ✶ refl

      q : (e ● (e ● x)) ● y ＝ e ● ((e ● x) ● y)
      q = α e (e ● x) y

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

      γ : ((e ● e) ● x) ● y ＝ e ● (x ● y)
      γ = ((e ● e) ● x) ● y ＝⟨ p ⟩
          (e ● (e ● x)) ● y ＝⟨ q ⟩
          e ● ((e ● x) ● y) ＝⟨ r ⟩
          e ● (e ● (x ● y)) ＝⟨ s ⟩
          e ● (x ● y)       ∎

      δ : ((e ● e) ● x) ● y ＝ e ● (x ● y)
      δ = ((e ● e) ● x) ● y ＝⟨ p ⟩
          (e ● (e ● x)) ● y ＝⟨ q ⟩
          e ● ((e ● x) ● y) ＝⟨ t ⟩
          e ● (x ● y)       ∎

      l-1 : γ ＝ δ
      l-1 = γ                   ＝⟨ refl ⟩
            p ∙ (q ∙ (r ∙ s))   ＝⟨ ap (p ∙_) (∙assoc q r s ⁻¹) ⟩
            p ∙ ((q ∙ r) ∙ s)   ＝⟨ (∙assoc p (q ∙ r) s) ⁻¹ ⟩
            (p ∙ (q ∙ r)) ∙ s   ＝⟨ ap (_∙ s) π ⟩
            (u ∙ v) ∙ s         ＝⟨ ∙assoc u v s ⟩
            u ∙ (v ∙ s)         ＝⟨ ap (λ v₁ → u ∙ v₁) φᵢ ⟩
            u ∙ w               ＝⟨ ap (u ∙_) (ap (𝓻 e ✶_) (𝓲𝓭 ⁻¹)) ⟩ 
            u ∙ w''             ＝⟨ φₐₛ (𝓻 e) refl refl ⟩
            w' ∙ α e x y        ＝⟨ ap (_∙ α e x y) (i ⁻¹) ⟩
            (p ∙ t') ∙ α e x y  ＝⟨ ∙assoc p t' (α e x y) ⟩
            p ∙ (t' ∙ α e x y)  ＝⟨ ap (p ∙_) ii ⁻¹ ⟩
            p ∙ (q ∙ t)         ∎ 
              where
                i : p ∙ t' ＝ w'
                i = p ∙ t' ＝⟨ 𝓘 (α e e x) (refl ✶ (𝓵 x)) refl refl ⟩
                    (α e e x ∙ (refl ✶ (𝓵 x))) ✶ refl
                           ＝⟨ ap (λ 𝓼 → 𝓼 ✶ refl) φᵢ ⟩
                    w'     ∎

                ii : q ∙ t ＝ t' ∙ α e x y
                ii = φₐₛ refl (𝓵 x) refl

      l-2 : r ∙ s ＝ t
      l-2 = cancel-left (cancel-left l-1)

      γ₁ : e ● ((e ● x) ● y) ＝ x ● y
      γ₁ = e ● ((e ● x) ● y) ＝⟨ 𝓵 ((e ● x) ● y) ⟩
           (e ● x) ● y       ＝⟨ α e x y ⟩
           e ● (x ● y)       ＝⟨ 𝓵 (x ● y) ⟩
           x ● y             ∎

      δ₁ : e ● ((e ● x) ● y) ＝ x ● y
      δ₁ = e ● ((e ● x) ● y) ＝⟨ 𝓵 ((e ● x) ● y) ⟩
           (e ● x) ● y       ＝⟨ (𝓵 x) ✶ refl ⟩
           x ● y             ∎

      l-3 : γ₁ ＝ δ₁
      l-3 = γ₁                                      ＝⟨ ∙assoc (𝓵 ((e ● x) ● y)) (α e x y) (𝓵 (x ● y)) ⁻¹ ⟩
            𝓵 ((e ● x) ● y) ∙ (α e x y) ∙ 𝓵 (x ● y) ＝⟨ ap (_∙ (𝓵 (x ● y))) (φₗ (α e x y) ⁻¹) ⟩
            r ∙ 𝓵 (e ● (x ● y)) ∙ 𝓵 (x ● y)         ＝⟨ ∙assoc r _ (𝓵 (x ● y)) ⟩
            r ∙ (𝓵 (e ● (x ● y)) ∙ 𝓵 (x ● y))       ＝⟨ ap (r ∙_) (φₗ (𝓵 (x ● y)) ⁻¹) ⟩
            r ∙ (s ∙ 𝓵 (x ● y))                     ＝⟨ ∙assoc r s (𝓵 (x ● y)) ⁻¹ ⟩
            (r ∙ s) ∙ 𝓵 (x ● y)                     ＝⟨ ap (_∙ (𝓵 (x ● y))) l-2 ⟩
            t ∙ 𝓵 (x ● y)                           ＝⟨ φₗ ((𝓵 x) ✶ refl) ⟩
            δ₁ ∎

      l-4 : (α e x y) ∙ 𝓵 (x ● y) ＝ (𝓵 x) ✶ refl
      l-4 = cancel-left l-3

\end{code}

⊗-assoc-neutral-r is a consequence too of ⊗-assoc-neutral and the
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
  have-⊗-assoc-neutral-r {x} {y} = cancel-left lemma-2
    where
      p : ((x ● y) ● e) ● e ＝ (x ● (y ● e)) ● e
      p = (α x y e) ✶ refl
      q : (x ● (y ● e)) ● e ＝ x ● ((y ● e) ● e)
      q = α x (y ● e) e
      q' : (x ● y) ● e ＝ x ● (y ● e)
      q' = α _ _ _
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
      v = α _ _ _

      γ δ ε η : ((x ● y) ● e) ● e ＝ x ● (y ● e)
      γ = p ∙ q ∙ r ∙ s
      δ = p ∙ t' ∙ q'
      ε = u ∙ v ∙ s
      η = s'' ∙ q'

      i : γ ＝ δ
      i = ((p ∙ q) ∙ r) ∙ s     ＝⟨ ∙assoc (p ∙ q) r s ⟩
          (p ∙ q) ∙ (r ∙ s)     ＝⟨ ap (p ∙ q ∙_) (𝓘 refl refl (α y e e) (refl ✶ (𝓵 e))) ⟩
          (p ∙ q) ∙ (refl ✶ (α y e e ∙ (refl ✶ 𝓵 e)))
                                ＝⟨ ap ((p ∙ q) ∙_) (ap (refl ✶_) φᵢ) ⟩
          p ∙ q ∙ t             ＝⟨ ∙assoc p q t ⟩
          p ∙ (q ∙ t)           ＝⟨ ap (p ∙_) (φₐₛ refl (𝓻 y) refl) ⟩
          p ∙ (t' ∙ q')         ＝⟨ (∙assoc p t' q') ⁻¹ ⟩
          p ∙ t' ∙ q'            ∎

      ii : γ ＝ ε
      ii = p ∙ q ∙ r ∙ s        ＝⟨ ap (_∙ s) (∙assoc p q r) ⟩
           (p ∙ (q ∙ r)) ∙ s    ＝⟨ ap (_∙ s) π ⟩
           u ∙ v ∙ s            ∎

      iii : ε ＝ η
      iii = u ∙ v ∙ s           ＝⟨ ∙assoc u v s ⟩
            u ∙ (v ∙ s)         ＝⟨ ap (u ∙_) (φₐₛ refl refl (𝓵 e)) ⟩
            u ∙ (s₁' ∙ q')      ＝⟨ ap (u ∙_) (ap (_∙ q') (ap (_✶ (𝓵 e)) 𝓲𝓭)) ⟩
            u ∙ (s' ∙ q')       ＝⟨ (∙assoc u s' q') ⁻¹ ⟩
            (u ∙ s') ∙ q'       ＝⟨ ap (_∙ q') φᵢ ⟩
            s'' ∙ q'            ∎

      iv : δ ＝ η
      iv = i ⁻¹ ∙ ii ∙ iii

      lemma : p ∙ t' ＝ s''
      lemma = p ∙ t'                    ＝⟨ ap ((p ∙ t') ∙_) (right-inverse q') ⟩
              (p ∙ t') ∙ (q' ∙ q' ⁻¹)   ＝⟨ ∙assoc (p ∙ t') q' (q' ⁻¹) ⁻¹ ⟩
              (p ∙ t' ∙ q') ∙ q' ⁻¹     ＝⟨ ap (_∙ q' ⁻¹) iv ⟩
              (s'' ∙ q') ∙ q' ⁻¹        ＝⟨ ∙assoc s'' q' (q' ⁻¹) ⟩
              s'' ∙ (q' ∙ q' ⁻¹)        ＝⟨ ap (s'' ∙_) (right-inverse q' ⁻¹) ⟩
              s''                       ∎

      μ ν : ((x ● y) ● e) ● e ＝ x ● y
      μ = ((x ● y) ● e) ● e  ＝⟨ 𝓻 ((x ● y) ● e) ⟩
           (x ● y) ● e       ＝⟨ α x y e ⟩
           x ● (y ● e)       ＝⟨ refl ✶ 𝓻 y ⟩
           x ● y             ∎

      ν = ((x ● y) ● e) ● e ＝⟨ 𝓻 ((x ● y) ● e) ⟩
          (x ● y) ● e       ＝⟨ 𝓻 (x ● y) ⟩
          x ● y             ∎

      lemma-2 : μ ＝ ν
      lemma-2 = 𝓻 ((x ● y) ● e) ∙ (α x y e ∙ refl ✶ 𝓻 y) ＝⟨ (∙assoc (𝓻 ((x ● y) ● e)) (α x y e) (refl ✶ 𝓻 y)) ⁻¹ ⟩
                (𝓻 ((x ● y) ● e) ∙ α x y e) ∙ refl ✶ 𝓻 y ＝⟨ ap (_∙ refl ✶ 𝓻 y) (φᵣ (α x y e) ⁻¹) ⟩
                (p ∙ 𝓻 (x ● (y ● e))) ∙ refl ✶ 𝓻 y       ＝⟨ ∙assoc p (𝓻 (x ● (y ● e))) (refl ✶ (𝓻 y)) ⟩
                p ∙ (𝓻 (x ● (y ● e)) ∙ refl ✶ 𝓻 y)       ＝⟨ ap (p ∙_) (φᵣ (refl ✶ (𝓻 y)) ⁻¹) ⟩
                p ∙ (t' ∙ 𝓻 (x ● y))                      ＝⟨ ∙assoc p t' (𝓻 (x ● y)) ⁻¹ ⟩
                (p ∙ t') ∙ 𝓻 (x ● y)                      ＝⟨ ap (_∙ 𝓻 (x ● y)) lemma ⟩
                s'' ∙ 𝓻 (x ● y)                           ＝⟨ φᵣ (𝓻 (x ● y)) ⟩
                ν                                          ∎

\end{code}

Finally, the axiom establishing that 𝓵 e ＝ 𝓻 e is also a consequence
of the others.

\begin{code}

  have-left-right-neutral-compat : left-right-neutral-compatibility X _●_ _✶_ e 𝓵 𝓻
  have-left-right-neutral-compat = cancel-left (lemma-3 ⁻¹)
    where
      lemma-1 : refl ✶ (𝓵 e) ＝ 𝓵 (e ● e)
      lemma-1 = refl ✶ (𝓵 e)                        ＝⟨ ap ((refl ✶ (𝓵 e)) ∙_) (right-inverse (𝓵 e)) ⟩
                (refl ✶ (𝓵 e)) ∙ ((𝓵 e) ∙ (𝓵 e) ⁻¹) ＝⟨ ∙assoc (refl ✶ (𝓵 e)) (𝓵 e) ((𝓵 e) ⁻¹) ⁻¹ ⟩
                ((refl ✶ (𝓵 e)) ∙ (𝓵 e)) ∙ (𝓵 e) ⁻¹ ＝⟨ ap (_∙ (𝓵 e) ⁻¹) (φₗ (𝓵 e)) ⟩
                (𝓵 (e ● e) ∙ (𝓵 e)) ∙ (𝓵 e) ⁻¹      ＝⟨ ∙assoc (𝓵 (e ● e)) (𝓵 e) (𝓵 e ⁻¹) ⟩
                𝓵 (e ● e) ∙ ((𝓵 e) ∙ (𝓵 e) ⁻¹)      ＝⟨ ap (𝓵 (e ● e) ∙_) (right-inverse (𝓵 e) ⁻¹) ⟩
                𝓵 (e ● e)                           ∎

      lemma-2 : (𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e) ＝ (𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e)
      lemma-2 = (𝓻 e) ✶ (𝓻𝓮𝒻𝓵 e)           ＝⟨ φᵢ ⁻¹ ⟩
                (α e e e) ∙ (refl ✶ (𝓵 e)) ＝⟨ ap ((α e e e) ∙_) lemma-1 ⟩
                (α e e e) ∙ (𝓵 (e ● e))    ＝⟨ have-⊗-assoc-neutral-l ⟩
                (𝓵 e) ✶ (𝓻𝓮𝒻𝓵 e) ∎

      lemma-3 : 𝓻 (e ● e) ∙ (𝓻 e) ＝ 𝓻 (e ● e) ∙ (𝓵 e)
      lemma-3 = 𝓻 (e ● e) ∙ (𝓻 e)      ＝⟨ φᵣ (𝓻 e) ⁻¹ ⟩
                ((𝓻 e) ✶ refl) ∙ (𝓻 e) ＝⟨ ap (_∙ (𝓻 e)) lemma-2 ⟩
                ((𝓵 e) ✶ refl) ∙ (𝓻 e) ＝⟨ φᵣ (𝓵 e) ⟩
                𝓻 (e ● e) ∙ (𝓵 e)       ∎

\end{code}
