/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexMirrorPairedBoundary.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.HexGenuineStripPhaseObstruction
import Def.StatisticalMechanics.Code.Universality.HexMirrorPairedBoundary


namespace StatMech.Universality

open Complex Set

open scoped BigOperators


namespace HexMirrorBoundaryPair

variable {V : Type*} [DecidableEq V]

variable {D : HexDomain V} {heading : V → Fin 3 → ℤ}


theorem unit_projection (Q : HexMirrorBoundaryPair D heading) :
    (∑ e ∈ Q.piece,
      hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) =
        Complex.I * ((2 * Real.cos Q.angle * Q.mass : ℝ) : ℂ) := by
  rw [piece, Finset.sum_union Q.disjoint]
  have hneg :
      (∑ e ∈ Q.neg,
        hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) =
      hexUnit Q.headNeg *
        (∑ e ∈ Q.neg, D.obs (D.mid e.vtx e.edge)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Q.hHeadNeg e he]
  have hpos :
      (∑ e ∈ Q.pos,
        hexUnit (heading e.vtx e.edge) * D.obs (D.mid e.vtx e.edge)) =
      hexUnit Q.headPos *
        (∑ e ∈ Q.pos, D.obs (D.mid e.vtx e.edge)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    rw [Q.hHeadPos e he]
  rw [hneg, hpos,
    hexUnitPhase_proj_complex Q.headNeg
      (Complex.exp ((-Q.angle : ℝ) * Complex.I) * (Q.mass : ℂ)) _ Q.phaseNeg,
    hexUnitPhase_proj_complex Q.headPos
      (Complex.exp ((Q.angle : ℝ) * Complex.I) * (Q.mass : ℂ)) _ Q.phasePos,
    ← mul_add]
  congr 1
  exact hexPhase_reflection_madeReal Q.angle Q.mass

end HexMirrorBoundaryPair
end StatMech.Universality
