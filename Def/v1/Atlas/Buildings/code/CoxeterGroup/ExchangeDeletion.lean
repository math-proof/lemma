/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Length
variable {B : Type*}


namespace CoxeterExchange

/-- Exchange Condition for $(W, S)$: for every reduced word $s_1 \cdots s_k$ and every
generator $s$ with $\ell(w s) < \ell(w)$, there exists an index $i$ such that
$s_1 \cdots \widehat{s_i} \cdots s_k = ws$. -/
def SatisfiesExchangeCondition {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (word : List B) (s : B),
    cs.IsReduced word →
    cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word) →
    ∃ (i : Fin word.length),
      cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s

/-- Deletion Condition for $(W, S)$: any non-reduced word $s_1 \cdots s_k$ (i.e.
$\ell(\prod s_i) < k$) admits two indices $i < j$ that can be deleted without
changing the product. -/
def SatisfiesDeletionCondition {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (word : List B),
    word.length > cs.length (cs.wordProd word) →
    ∃ (i j : Fin word.length), i < j ∧
      cs.wordProd ((word.eraseIdx j).eraseIdx i) = cs.wordProd word

/-- Corollary of the Exchange Condition: if $s, t \in S$ are ascents on both sides of
$w$, then either $\ell(swt) = \ell(w) + 2$ or $swt = w$. -/
def ExchangeCorollary {W : Type*} [Group W]
    (M : CoxeterMatrix B) (cs : CoxeterSystem M W) : Prop :=
  ∀ (w : W) (s t : B),
    cs.length (cs.simple s * w) = cs.length w + 1 →
    cs.length (w * cs.simple t) = cs.length w + 1 →
    cs.length (cs.simple s * w * cs.simple t) = cs.length w + 2 ∨
    cs.simple s * w * cs.simple t = w

end CoxeterExchange
