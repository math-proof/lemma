/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part119
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem boxBoundary3_surfaceVec_face_cases
    (n : ℕ) (v : FK.boxVerts 3 n) (hv : FK.boxBoundary 3 n v) :
    let x : ℝ := ((v : Lattice.Site 3) 0 : ℝ)
    let y : ℝ := ((v : Lattice.Site 3) 1 : ℝ)
    let z : ℝ := ((v : Lattice.Site 3) 2 : ℝ)
    x = (n : ℝ) ∨ x = -(n : ℝ) ∨
    y = (n : ℝ) ∨ y = -(n : ℝ) ∨
    z = (n : ℝ) ∨ z = -(n : ℝ) := by
  rw [FK.boxBoundary, Lattice.mem_vertexBoundary] at hv
  have hnot : ¬ ∀ i : Fin 3,
      (((v : Lattice.Site 3) i).natAbs ≤ n - 1) := hv.2
  push Not at hnot
  rcases hnot with ⟨i, hi⟩
  have hle : ((v : Lattice.Site 3) i).natAbs ≤ n := hv.1 i
  have habs : ((v : Lattice.Site 3) i).natAbs = n := by omega
  rcases Int.natAbs_eq_iff.mp habs with hpos | hneg
  · fin_cases i
    · left
      norm_num at hpos ⊢
      exact_mod_cast hpos
    · right; right; left
      norm_num at hpos ⊢
      exact_mod_cast hpos
    · right; right; right; right; left
      norm_num at hpos ⊢
      exact_mod_cast hpos
  · fin_cases i
    · right; left
      norm_num at hneg ⊢
      exact_mod_cast hneg
    · right; right; right; left
      norm_num at hneg ⊢
      exact_mod_cast hneg
    · right; right; right; right; right
      norm_num at hneg ⊢
      exact_mod_cast hneg


end Exact3D
end StatMech
