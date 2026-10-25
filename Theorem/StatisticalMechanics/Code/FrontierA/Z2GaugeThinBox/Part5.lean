/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeThinBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeThinBox.Part4
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

@[simp] theorem thinBoxSurfaceEquiv_apply (n : ℕ)
    (A : {A : Finset (thinBoxPlaquette n) //
      A ∈ gaugeClosedSurfaceFamily (thinBoxIncidence n)}) :
    (thinBoxSurfaceEquiv n A).1 =
      A.1.map (dualPlaquetteEmbedding (thinBoxDualEdge n)) :=
  rfl


theorem thinBox_gaugePartition_isingDuality (n : ℕ)
    (K : thinBoxPlaquette n → ℝ) (hK : ∀ p, 0 < K p) :
    (Real.exp (∑ e ∈ (thinBoxDualGraph n).edgeFinset,
          dualIsingCoupling (thinBoxDualEdge n) K e) * 2) *
        gaugePartition (thinBoxIncidence n) K =
      ((2 : ℝ) ^ Fintype.card thinBoxGaugeEdge *
          ∏ p : thinBoxPlaquette n, Real.cosh (K p)) *
        ZJ (thinBoxDualGraph n).edgeFinset
          (dualIsingCoupling (thinBoxDualEdge n) K) (fun _ => 0) := by
  exact gaugePartition_isingDuality
    (SimpleGraph.pathGraph_preconnected (n + 1))
    (thinBoxIncidence n) K hK (thinBoxDualEdge n)
    (thinBoxSurfaceEquiv n) (thinBoxSurfaceEquiv_apply n)

end
end StatMech.FrontierA
