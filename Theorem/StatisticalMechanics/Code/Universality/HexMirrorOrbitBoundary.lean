/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorOrbitBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexMirrorPairFromReflection.Part5
import Def.StatisticalMechanics.Code.Universality.HexMirrorOrbitBoundary


namespace StatMech.Universality

open Complex HexWalk

open scoped BigOperators


namespace HexFixedBoundaryPoint

variable {V : Type*} [DecidableEq V]

variable {D : HexDomain V} {heading : V → Fin 3 → ℤ}


theorem unit_projection (Q : HexFixedBoundaryPoint D heading) :
    (∑ e ∈ Q.piece,
      hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) =
        Complex.I * (Q.mass : ℂ) := by
  rw [piece, Finset.sum_singleton, Q.hHead]
  exact hexUnitPhase_proj_complex Q.head (Q.mass : ℂ)
    (D.obs (D.mid Q.incidence.vtx Q.incidence.edge)) Q.phase

end HexFixedBoundaryPoint
end StatMech.Universality
