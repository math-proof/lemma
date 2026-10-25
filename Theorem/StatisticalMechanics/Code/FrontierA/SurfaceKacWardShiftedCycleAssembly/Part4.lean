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
import Def.StatisticalMechanics.Code.FrontierA.SurfaceKacWardShiftedCycleAssembly.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Onsager Polynomial

universe u

theorem kwGraphFormalLogCoeff_cycle_of_shifted_phase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    {root : V} (p : G.Walk root root) (hp : p.IsCycle)
    (hphase :
      letI : NeZero p.darts.length :=
        ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
          (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
      kwLoopPhaseProduct phase (kwGraphCycleDartLoop p) =
        -surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset) :
    kwGraphFormalLogCoeff G phase (ons_finsetExponent p.edges.toFinset) =
      surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  let coefficient :=
    surfaceSpinCycleCoefficient edgeClass lambda p.edges.toFinset
  have hscalar : kwGraphLoopScalar G phase (kwGraphCycleDartLoop p) =
      -coefficient := by
    rw [kwGraphCycleDartLoop_scalar_eq_phaseProduct G phase p hp]
    exact hphase
  have hcoeffNe : coefficient ≠ 0 := by
    unfold coefficient surfaceSpinCycleCoefficient
    exact Complex.ofReal_ne_zero.mpr (surfaceParitySign_ne_zero _)
  have hscalarNe : kwGraphLoopScalar G phase
      (kwGraphCycleDartLoop p) ≠ 0 := by
    rw [hscalar]
    exact neg_ne_zero.mpr hcoeffNe
  have hd : kwGraphCycleDartLoop p ∈
      kwGraphSquarefreeLoopFinset G phase p.edges.toFinset := by
    rw [kwGraph_mem_squarefreeLoopFinset]
    exact ⟨kwGraphCycleDartLoop_exponent G p hp, hscalarNe⟩
  rw [kwGraphFormalLogCoeff_squarefree_of_mem_reversalInvariant'
    G phase hrev hdeg p.edges.toFinset (kwGraphCycleDartLoop p) hd,
    hscalar]
  ring

theorem kwGraphWeightedCycleLog_of_shifted_simpleCyclePhase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hphase : KWGraphShiftedSimpleCyclePhase
      G phase edgeClass lambda) :
    KWGraphWeightedCycleLog G phase
      (surfaceSpinCycleCoefficient edgeClass lambda) := by
  constructor
  · intro root p hp
    exact kwGraphFormalLogCoeff_cycle_of_shifted_phase
      G phase edgeClass lambda hrev hdeg p hp (hphase p hp)
  · exact kwGraphFormalLogCoeff_squarefree_cycle_of_ne_zero
      G phase hdeg

theorem surface_kacWard_shifted_det_square_of_simpleCyclePhase
    {g : Nat} {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq G.Dart]
    (phase : G.Dart -> G.Dart -> Complex)
    (edgeClass : Sym2 V -> SurfaceHomology g)
    (lambda : SurfaceSpinStructure g)
    (hrev : KWGraphLoopReversalInvariant G phase)
    (hphase : KWGraphShiftedSimpleCyclePhase
      G phase edgeClass lambda)
    (hisotropic : SurfaceDisjointCycleIsotropic G edgeClass)
    (hdeg : ∀ vertex, G.degree vertex <= 3)
    (hnonsquare : ∀ m : Sym2 V →₀ Nat,
      ¬ ons_IsSquarefreeExponent m ->
        MvPowerSeries.coeff m (kwGraphFormalRoot G phase) = 0)
    (weight : Sym2 V -> Complex) :
    (1 - kwGraphTransition G weight phase).det =
      surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
  apply surface_kacWard_shifted_det_square_of_cycle_phase
    G phase edgeClass lambda
  · exact kwGraphWeightedCycleLog_of_shifted_simpleCyclePhase
      G phase edgeClass lambda hrev hdeg hphase
  · exact hisotropic
  · exact hdeg
  · exact hnonsquare

end StatMech.FrontierA
