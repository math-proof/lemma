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
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part118
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

theorem freeQ2BoundaryVertexPointwise_of_envelopeAtLeastMass
    (henv :
      FreeQ2BoundaryVertexEnvelopeAtLeastMassPositiveSubcritical) :
    FreeQ2BoundaryProfileBoundaryVertexPointwiseSameMassPositiveSubcritical := by
  intro β hβpos hβc Alo AfkHi mass hmass hconn
  rcases henv β hβpos hβc Alo AfkHi mass hmass hconn with
    ⟨Aenv, envelope, boundaryMass, hmass_le, hAenv, hpoint, henvHi⟩
  refine ⟨Aenv, hAenv, ?_⟩
  filter_upwards [hpoint, henvHi, hAenv.1] with
    n hpoint_n henv_n hAenv_pos
  intro v hv
  have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
  have hmass_mul : mass * (n : ℝ) ≤ boundaryMass * (n : ℝ) :=
    mul_le_mul_of_nonneg_right hmass_le hn_nonneg
  have hexp_le :
      Real.exp (-(boundaryMass * (n : ℝ))) ≤
        Real.exp (-(mass * (n : ℝ))) := by
    exact Real.exp_le_exp.mpr (by linarith)
  calc
    ((FK.wiredFiniteMeasure 3 n (Ising.pOfBeta_pos hβpos)
        (Ising.pOfBeta_lt_one β) (by norm_num : (0 : ℝ) < 2))
      : Measure (ConfigSpace (Sym2 (Lattice.Site 3)))).real
        (FK.boxConnEvent 3 n (IsingFK.boxOrigin 3 n) v)
        ≤ envelope n := hpoint_n v hv
    _ ≤ Aenv n * Real.exp (-(boundaryMass * (n : ℝ))) := henv_n
    _ ≤ Aenv n * Real.exp (-(mass * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left hexp_le (le_of_lt hAenv_pos)


end Exact3D
end StatMech
