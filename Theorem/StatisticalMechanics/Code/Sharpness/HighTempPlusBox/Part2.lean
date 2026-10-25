/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/HighTempPlusBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.HighTempVertexField.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonPlusLimit.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.MeanfieldIsingMass.Part3
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Def.StatisticalMechanics.Code.Sharpness.HighTempPlusBox.Part2
open Finset SimpleGraph MeasureTheory
open scoped BigOperators Classical


namespace StatMech

namespace Sharpness

open Ising Lattice Percolation

variable {d : ℕ}


theorem unitEdgeCoupling_nonneg {V : Type*} (G : SimpleGraph V)
    (e : Sym2 V) : 0 ≤ unitEdgeCoupling G e := by
  unfold unitEdgeCoupling
  split <;> norm_num

@[simp] theorem unitEdgeCoupling_edgeFinset {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {e : Sym2 V} (he : e ∈ G.edgeFinset) :
    unitEdgeCoupling G e = 1 := by
  rw [unitEdgeCoupling, if_pos]
  exact SimpleGraph.mem_edgeFinset.mp he


theorem gvPlusWeight_eq_vertexFieldWeight (Lambda : Finset (Site d))
    (beta : ℝ) (tau : ConfigSpace {v // v ∈ Lambda}) :
    gvWeight (plusField d) Lambda beta 0 tau =
      vertexFieldWeight (graphS d Lambda) beta
        (unitEdgeCoupling (graphS d Lambda))
        (plusBoundaryField Lambda) tau := by
  unfold gvWeight gvEnergy vertexFieldWeight
  rw [plusTouch_bondSum]
  simp only [zero_mul, sub_zero]
  have hedge :
      (∑ e ∈ (graphS d Lambda).edgeFinset,
          unitEdgeCoupling (graphS d Lambda) e * bond tau e) =
        ∑ e ∈ (graphS d Lambda).edgeFinset, bond tau e := by
    apply Finset.sum_congr rfl
    intro e he
    rw [unitEdgeCoupling_edgeFinset (graphS d Lambda) he, one_mul]
  rw [hedge]
  congr 1
  ring

theorem gvPlusZ_eq_vertexFieldZ (Lambda : Finset (Site d)) (beta : ℝ) :
    gvZ (plusField d) Lambda beta 0 =
      vertexFieldZ (graphS d Lambda) beta
        (unitEdgeCoupling (graphS d Lambda))
        (plusBoundaryField Lambda) := by
  unfold gvZ vertexFieldZ
  apply Finset.sum_congr rfl
  intro tau _
  exact gvPlusWeight_eq_vertexFieldWeight Lambda beta tau

theorem gvPlusProb_eq_vertexField (Lambda : Finset (Site d))
    (beta : ℝ) (tau : ConfigSpace {v // v ∈ Lambda}) :
    gvProb (plusField d) Lambda beta 0 tau =
      vertexFieldWeight (graphS d Lambda) beta
          (unitEdgeCoupling (graphS d Lambda))
          (plusBoundaryField Lambda) tau /
        vertexFieldZ (graphS d Lambda) beta
          (unitEdgeCoupling (graphS d Lambda))
          (plusBoundaryField Lambda) := by
  unfold gvProb
  rw [gvPlusWeight_eq_vertexFieldWeight, gvPlusZ_eq_vertexFieldZ]


theorem integral_gvMeasure_eq_sum (eta : ConfigSpace (Site d))
    (Lambda : Finset (Site d)) (beta h : ℝ)
    (f : ConfigSpace (Site d) → ℝ) :
    ∫ omega, f omega ∂(gvMeasure eta Lambda beta h) =
      ∑ tau : ConfigSpace {v // v ∈ Lambda},
        gvProb eta Lambda beta h tau * f (gvGlue eta Lambda tau) := by
  unfold gvMeasure
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl (fun tau _ ↦ ?_)
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (gvProb_nonneg eta Lambda beta h tau)]
  · intro tau _
    exact (integrable_dirac (by simp [enorm_eq_nnnorm])).smul_measure (by simp)


theorem spinProd_sourcePair {V : Type*} [Fintype V] [DecidableEq V]
    (tau : ConfigSpace V) (a b : V) :
    spinProd (sourcePair a b) tau = spin tau a * spin tau b := by
  by_cases hab : a = b
  · subst b
    rw [sourcePair_self, spinProd_empty, spin_sq]
  · rw [sourcePair_eq_pair hab]
    simp [spinProd, hab]


theorem gvPlus_pair_eq_vertexField (Lambda : Finset (Site d))
    (beta : ℝ) (a b : {v // v ∈ Lambda}) :
    (∫ omega, spin omega a.1 * spin omega b.1
        ∂(gvPlusMeasure Lambda beta 0)) =
      vertexFieldTwoPoint (graphS d Lambda) beta
        (unitEdgeCoupling (graphS d Lambda))
        (plusBoundaryField Lambda) a b := by
  unfold gvPlusMeasure
  rw [integral_gvMeasure_eq_sum]
  unfold vertexFieldTwoPoint vertexFieldExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro tau _
  rw [gvPlusProb_eq_vertexField]
  have hspin (x : {v // v ∈ Lambda}) :
      spin (gvGlue (plusField d) Lambda tau) x.1 = spin tau x := by
    simp [spin, gvGlue, x.2]
  rw [hspin a, hspin b, spinProd_sourcePair]
  ring


theorem twoPointJ_congr_on_edges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (beta : ℝ) (J K : Sym2 V → ℝ)
    (hJK : ∀ e ∈ G.edgeFinset, J e = K e) (a b : V) :
    twoPointJ G beta J a b = twoPointJ G beta K a b := by
  have hweight (tau : ConfigSpace V) :
      boltzmannJ G beta J tau = boltzmannJ G beta K tau := by
    unfold boltzmannJ
    apply congrArg Real.exp
    apply congrArg (fun r ↦ beta * r)
    apply Finset.sum_congr rfl
    intro e he
    rw [hJK e he]
  unfold twoPointJ expectationJ partitionJ
  simp_rw [hweight]


theorem twoPointJ_couplingIn_unitEdge (Lambda : Finset (Site d))
    (beta : ℝ) (T : Finset {v // v ∈ Lambda})
    (a b : {v // v ∈ Lambda}) :
    twoPointJ (graphS d Lambda) beta
        (couplingIn (unitEdgeCoupling (graphS d Lambda)) T) a b =
      twoPointJ (graphS d Lambda) beta (couplingIn (fun _ ↦ 1) T) a b := by
  apply twoPointJ_congr_on_edges
  intro e he
  simp only [couplingIn]
  split
  · rw [unitEdgeCoupling_edgeFinset (graphS d Lambda) he]
  · rfl


end Sharpness
end StatMech
