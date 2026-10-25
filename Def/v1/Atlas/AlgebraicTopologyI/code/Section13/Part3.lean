/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section13.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section12
import Def.v1.Atlas.AlgebraicTopologyI.code.Section12.Part2
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Analysis.Convex.Combination
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Module.Convex
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section13
open Finset BigOperators Set Metric


namespace AlgebraicTopologyI

/-- Lemma 13.4 (chain-level witness). For every `k`, the `k`-fold iterate
`$^k` of the subdivision operator is chain-homotopic to the identity on
`S_*(X)`. The witness is built by induction on `k`, composing the one-step
subdivision chain homotopy with the previous iterate. -/
def iteratedSubdivisionHomotopy (X : TopCat.{0}) (k : ℕ) :
    Homotopy
      (endoPow (subdivisionOperator.app X) k)
      (𝟙 (singularChainFunctorZ.obj X)) := by
  induction k with
  | zero => exact Homotopy.ofEq (endoPow_zero _)
  | succ k IH =>
    have H := subdivisionChainHomotopy X
    have h1 := H.compRight (endoPow (subdivisionOperator.app X) k)
    have h2 :
        (𝟙 (singularChainFunctorZ.obj X)) ≫
          endoPow (subdivisionOperator.app X) k =
        endoPow (subdivisionOperator.app X) k :=
      Category.id_comp _
    exact h1.trans ((Homotopy.ofEq h2).trans IH)

end AlgebraicTopologyI
