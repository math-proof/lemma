/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardShiftedCycleAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardQuadraticAssembly.Part4
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardFlatSpinor
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAngularSplitUnitCycleReduction
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardPortChainHomology
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardLocalAngularSplitCycleReversal
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedCycleAssembly.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u

theorem kwAngularSplit_shifted_det_square_of_cyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (edgeClass : Sym2 (KWDartPort G) -> SurfaceHomology 1)
    (lambda : SurfaceSpinStructure 1)
    (hphase : KWAngularSplitShiftedCyclePhase
      embedding edgeClass lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      edgeClass)
    (weight : Sym2 (KWDartPort G) -> Complex) :
    (1 - kwGraphTransition
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      weight (kwAngularSplitPhase embedding)).det =
      surfaceQuadraticEvenPolynomial
        (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
        edgeClass lambda weight ^ 2 := by
  apply surface_kacWard_shifted_det_square_of_simpleCyclePhase
  · exact kwAngularSplit_loopReversalInvariant embedding
  · exact hphase
  · exact hisotropic
  · exact kwAngularSplit_degree_le_three embedding
  · exact kwAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree embedding


theorem surface_kacWard_original_of_angularSplit_shifted_cyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (embedding : KWStraightLineEmbedding G)
    (edgeClass : Sym2 V -> SurfaceHomology 1)
    (hdiag : ∀ v, edgeClass s(v, v) = 0)
    (lambda : SurfaceSpinStructure 1)
    (weight : Sym2 V -> Complex)
    (hphase : KWAngularSplitShiftedCyclePhase embedding
      (kwOrderedSplitEdgeClass edgeClass) lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph G (kwAngularPortOrder embedding))
      (kwOrderedSplitEdgeClass edgeClass)) :
    (1 - kwGraphTransition G weight embedding.turnPhase).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  rw [<- kwAngularSplit_det_eq_original embedding weight]
  rw [← kwOrderedSplit_surfaceQuadraticEvenPolynomial_eq
    G (kwAngularPortOrder embedding) edgeClass hdiag lambda weight]
  exact kwAngularSplit_shifted_det_square_of_cyclePhase embedding
    (kwOrderedSplitEdgeClass edgeClass) lambda hphase hisotropic
    (kwOrderedSplitWeight G weight)


end StatMech.FrontierA
