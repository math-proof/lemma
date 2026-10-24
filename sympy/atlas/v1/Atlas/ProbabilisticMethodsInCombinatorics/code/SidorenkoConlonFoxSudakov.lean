/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/SidorenkoConlonFoxSudakov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.Sidorenko
import Lemma.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter10.Sidorenko

set_option maxHeartbeats 400000

noncomputable section

namespace Sidorenko

/-- A bipartite graph $F$ on $A \sqcup B$ has a "universal vertex" if some vertex in $A$
is adjacent to every vertex of $B$, or some vertex in $B$ is adjacent to every vertex of
$A$. This is the hypothesis of the Conlon-Fox-Sudakov theorem on Sidorenko's conjecture. -/
def HasUniversalVertex {A : Type*} {B : Type*}
    (F : SimpleGraph (A ⊕ B)) : Prop :=
  (∃ a : A, ∀ b : B, F.Adj (Sum.inl a) (Sum.inr b)) ∨
  (∃ b : B, ∀ a : A, F.Adj (Sum.inr b) (Sum.inl a))
