/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionThermodynamic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionThermodynamic.Part3
open Filter Topology Set
open scoped BigOperators Topology


namespace StatMech.FrontierA

noncomputable section

theorem cubicalSquareWilsonDensity_eq_disorderDensity
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    cubicalSquareWilsonDensity beta n = cubicalSquareDisorderDensity beta n := by
  rw [cubicalSquareWilsonDensity, cubicalSquareDisorderDensity,
    cubicalSquareWilsonFreeEnergy_eq_disorderFreeEnergy hbeta n]


theorem cubicalSquareWilsonDensity_mem_Icc
    {beta : Real} (hbeta : 0 < beta) (n : Nat) :
    cubicalSquareWilsonDensity beta n ∈
      Set.Icc 0 (2 * gaugeDualCoupling beta) := by
  let L := n + 1
  have hL : 0 < L := by omega
  have hcost := cubicalXYWilsonFreeEnergy_mem_Icc
    hL hL hL (0 : Fin (L + 1))
      (fun _ : CubicalPlaquette L L L => beta) (fun _ => hbeta)
  have hdual : 0 < gaugeDualCoupling beta := gaugeDualCoupling_pos hbeta
  constructor
  · rw [cubicalSquareWilsonDensity]
    apply div_nonneg
    · simpa [cubicalSquareWilsonFreeEnergy, L] using hcost.1
    · exact sq_nonneg _
  · have harea : (0 : Real) < (L : Real) ^ 2 := by positivity
    rw [cubicalSquareWilsonDensity]
    apply (div_le_iff₀ harea).2
    have hupper := cubicalXYWilsonFreeEnergy_le_area_mul_dualCoupling
      hL hL hL (0 : Fin (L + 1)) beta hbeta
    have hupper' : cubicalSquareWilsonFreeEnergy beta n ≤
        2 * (L * L : Nat) * gaugeDualCoupling beta := by
      simpa [cubicalSquareWilsonFreeEnergy, L] using hupper
    rw [cubicalSquareWilsonFreeEnergy]
    change -Real.log _ ≤ _
    calc
      -Real.log _ ≤ 2 * (L * L : Nat) * gaugeDualCoupling beta := by
        simpa [cubicalSquareWilsonFreeEnergy] using hupper'
      _ = 2 * gaugeDualCoupling beta * (L : Real) ^ 2 := by
        push_cast
        ring


theorem cubicalSquareDisorderDensity_tendsto_iff_wilsonDensity
    {beta tau : Real} (hbeta : 0 < beta) :
    Tendsto (cubicalSquareDisorderDensity beta) atTop (nhds tau) ↔
      Tendsto (cubicalSquareWilsonDensity beta) atTop (nhds tau) := by
  constructor <;> intro h
  · exact h.congr' (Filter.Eventually.of_forall fun n =>
      (cubicalSquareWilsonDensity_eq_disorderDensity hbeta n).symm)
  · exact h.congr' (Filter.Eventually.of_forall fun n =>
      cubicalSquareWilsonDensity_eq_disorderDensity hbeta n)


theorem exists_cubicalSquareSurfaceRate_subseq
    {beta : Real} (hbeta : 0 < beta) :
    ∃ tau ∈ Set.Icc 0 (2 * gaugeDualCoupling beta),
      ∃ phi : Nat → Nat, StrictMono phi ∧
        Tendsto (cubicalSquareWilsonDensity beta ∘ phi) atTop (nhds tau) ∧
        Tendsto (cubicalSquareDisorderDensity beta ∘ phi) atTop (nhds tau) := by
  obtain ⟨tau, htau, phi, hphi, hwilson⟩ :=
    isCompact_Icc.tendsto_subseq
      (fun n => cubicalSquareWilsonDensity_mem_Icc hbeta n)
  refine ⟨tau, htau, phi, hphi, hwilson, ?_⟩
  exact hwilson.congr' (Filter.Eventually.of_forall fun n => by
    simp only [Function.comp_apply]
    exact cubicalSquareWilsonDensity_eq_disorderDensity hbeta (phi n))

end
end StatMech.FrontierA
