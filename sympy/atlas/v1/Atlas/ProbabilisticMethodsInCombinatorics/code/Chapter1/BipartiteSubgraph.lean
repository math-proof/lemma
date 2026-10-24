/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter1/BipartiteSubgraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
open Finset BigOperators SimpleGraph

namespace BipartiteSubgraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Boolean inequality `!=` is symmetric: $(f(a) \neq f(b)) = (f(b) \neq f(a))$. -/
lemma bne_symm {V : Type*} (f : V → Bool) (a b : V) :
    (f a != f b) = (f b != f a) := by
  rcases Bool.eq_false_or_eq_true (f a) with ha | ha <;>
    rcases Bool.eq_false_or_eq_true (f b) with hb | hb <;> simp [ha, hb]

/-- For a Boolean labelling `f : V → Bool`, `boolCut f e` returns `true` when the
unordered pair `e = s(u, v)` is a cut edge, i.e. `f u ≠ f v`. -/
def boolCut (f : V → Bool) : Sym2 V → Bool :=
  Sym2.lift ⟨fun u v => f u != f v, bne_symm f⟩

omit [Fintype V] [DecidableEq V] in
/-- Evaluation of `boolCut` on an explicit pair `s(u, v)`. -/
@[simp] lemma boolCut_mk (f : V → Bool) (u v : V) :
    boolCut f s(u, v) = (f u != f v) :=
  Sym2.lift_mk _ u v

/-- `flipAt v f` is the Boolean labelling obtained from `f` by negating its value at `v`. -/
def flipAt {V : Type*} [DecidableEq V] (v : V) (f : V → Bool) : V → Bool :=
  Function.update f v (!f v)

/-- The cut subgraph of `G` induced by a Boolean labelling `f`: the subgraph consisting
of edges `{u, v}` of `G` with `f u ≠ f v`. -/
def cutGraph {V : Type*} (G : SimpleGraph V) (f : V → Bool) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ f u ≠ f v
  symm _ _ := fun ⟨h1, h2⟩ => ⟨G.symm h1, Ne.symm h2⟩
  loopless := ⟨fun _ h => absurd rfl h.2⟩
