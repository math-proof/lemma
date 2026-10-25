/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionCondition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
variable {B : Type*}


namespace Garrett.ExchangeDeletion

/-- The exchange condition for a Coxeter system: if right multiplying a
reduced word $\omega$ by $s_i$ decreases length, there is some index $i$ such
that erasing the $i$-th letter from $\omega$ produces a word with product
$\omega \cdot s$. -/
def SatisfiesExchangeCondition {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (word : List B) (s : B),
    cs.IsReduced word →
    cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word) →
    ∃ (i : Fin word.length),
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s

/-- The deletion condition: if a word is non-reduced, two letters can be erased
without changing its product. Formally, if $\mathtt{word.length} >
\ell(\mathtt{wordProd}\,\mathtt{word})$ then there exist $i < j$ such that
erasing positions $i$ and $j$ leaves the product unchanged. -/
def SatisfiesDeletionCondition {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (word : List B),
    word.length > cs.length (cs.wordProd word) →
    ∃ (i j : Fin word.length), i < j ∧
      cs.wordProd ((word.eraseIdx j).eraseIdx i) = cs.wordProd word

/-- Corollary of the exchange condition used in subexpression arguments: if both
$\ell(sw) = \ell(w) + 1$ and $\ell(wt) = \ell(w) + 1$ hold, then either
$\ell(swt) = \ell(w) + 2$ or $swt = w$. -/
def ExchangeCorollary {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (w : W) (s t : B),
    cs.length (cs.simple s * w) = cs.length w + 1 →
    cs.length (w * cs.simple t) = cs.length w + 1 →
    cs.length (cs.simple s * w * cs.simple t) = cs.length w + 2 ∨
    cs.simple s * w * cs.simple t = w

end Garrett.ExchangeDeletion
