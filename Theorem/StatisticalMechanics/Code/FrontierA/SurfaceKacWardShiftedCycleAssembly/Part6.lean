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
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedCycleAssembly.Part6
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u

theorem kwLocalAngularSplit_shifted_det_square_of_cyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (edgeClass : Sym2 (KWDartPort G) -> SurfaceHomology 1)
    (lambda : SurfaceSpinStructure 1)
    (hphase : KWLocalAngularSplitShiftedCyclePhase
      data edgeClass lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph G data.order) edgeClass)
    (weight : Sym2 (KWDartPort G) -> Complex) :
    (1 - kwGraphTransition
      (kwOrderedDartPortSplitGraph G data.order)
      weight (kwLocalAngularSplitPhase data)).det =
      surfaceQuadraticEvenPolynomial
        (kwOrderedDartPortSplitGraph G data.order)
        edgeClass lambda weight ^ 2 := by
  apply surface_kacWard_shifted_det_square_of_simpleCyclePhase
  · exact kwLocalAngularSplit_loopReversalInvariant data
  · exact hphase
  · exact hisotropic
  · exact kwOrderedDartPortSplitGraph_degree_le_three G data.order
  · exact kwLocalAngularSplit_formalRoot_coeff_eq_zero_of_not_squarefree data


theorem surface_kacWard_original_of_localAngularSplit_shifted_cyclePhase
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (data : KWLocalAngularData G)
    (edgeClass : Sym2 V -> SurfaceHomology 1)
    (hdiag : forall v, edgeClass s(v, v) = 0)
    (lambda : SurfaceSpinStructure 1)
    (weight : Sym2 V -> Complex)
    (hphase : KWLocalAngularSplitShiftedCyclePhase data
      (kwOrderedSplitEdgeClass edgeClass) lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic
      (kwOrderedDartPortSplitGraph G data.order)
      (kwOrderedSplitEdgeClass edgeClass)) :
    (1 - kwGraphTransition G weight data.phase).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  rw [<- kwLocalAngularSplit_det_eq_original data weight]
  rw [← kwOrderedSplit_surfaceQuadraticEvenPolynomial_eq
    G data.order edgeClass hdiag lambda weight]
  exact kwLocalAngularSplit_shifted_det_square_of_cyclePhase data
    (kwOrderedSplitEdgeClass edgeClass) lambda hphase hisotropic
    (kwOrderedSplitWeight G weight)

end StatMech.FrontierA
