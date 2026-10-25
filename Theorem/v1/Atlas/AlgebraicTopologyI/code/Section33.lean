/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section33.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33
open CategoryTheory AlgebraicTopology Limits


noncomputable section

/-- Index-shape compatibility lemma: for the descending complex shape on `ℕ`,
the predecessor of `p` equals the successor of `p` for the ascending shape.
Both equal `p + 1`. Used to reconcile homological and cohomological indexing. -/
lemma down_prev_eq_up_next (p : ℕ) :
    (ComplexShape.down ℕ).prev p = (ComplexShape.up ℕ).next p := by
  rw [ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (p + 1) p from rfl),
      ComplexShape.next_eq' _ (show (ComplexShape.up ℕ).Rel p (p + 1) from rfl)]

/-- Index-shape compatibility lemma: for the descending complex shape on `ℕ`,
the successor of `p` equals the predecessor of `p` for the ascending shape.
Used to reconcile homological and cohomological indexing. -/
lemma down_next_eq_up_prev (p : ℕ) :
    (ComplexShape.down ℕ).next p = (ComplexShape.up ℕ).prev p := by
  rcases p with _ | p
  · simp [ComplexShape.next, ComplexShape.prev, ComplexShape.down, ComplexShape.up]
  · rw [ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (p + 1) p by simp [ComplexShape.down]),
        ComplexShape.prev_eq' _ (show (ComplexShape.up ℕ).Rel p (p + 1) by simp [ComplexShape.up])]

end
