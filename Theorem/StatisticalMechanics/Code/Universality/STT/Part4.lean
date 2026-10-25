/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/STT.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Universality.STT.Part4
open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

theorem prob_def (p0 p1 p2 : ℝ) (pat : LocalConfig → Bool) :
    triProb p0 p1 p2 pat = starProb p0 p1 p2 pat := rfl


theorem stt_AB (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatAB = starProb (1 - p0) (1 - p1) (1 - p2) starPatAB := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatAB, starPatAB,
    triAB, triAC, triBC, starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num


theorem stt_AC (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatAC = starProb (1 - p0) (1 - p1) (1 - p2) starPatAC := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatAC, starPatAC,
    triAB, triAC, triBC, starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num


theorem stt_BC (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatBC = starProb (1 - p0) (1 - p1) (1 - p2) starPatBC := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatBC, starPatBC,
    triAB, triAC, triBC, starAB, starAC, starBC, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num


theorem stt_ABC_sub (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatABC - starProb (1 - p0) (1 - p1) (1 - p2) starPatABC
      = kappaTri p0 p1 p2 := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatABC, starPatABC,
    triAB, triAC, triBC, starAB, starAC, starBC, kappaTri,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring


theorem stt_Sep_sub (p0 p1 p2 : ℝ) :
    triProb p0 p1 p2 triPatSep - starProb (1 - p0) (1 - p1) (1 - p2) starPatSep
      = -kappaTri p0 p1 p2 := by
  simp only [triProb, starProb, localWeight, edgeWeight, triPatSep, starPatSep,
    triAB, triAC, triBC, starAB, starAC, starBC, kappaTri,
    Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num
  ring


theorem stt_ABC (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) :
    triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC := by
  have := stt_ABC_sub p0 p1 p2
  rw [h] at this; linarith


theorem stt_Sep (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) :
    triProb p0 p1 p2 triPatSep = starProb (1 - p0) (1 - p1) (1 - p2) starPatSep := by
  have := stt_Sep_sub p0 p1 p2
  rw [h] at this; linarith


theorem starTriangle_connectivity (p0 p1 p2 : ℝ) (h : IsCriticalTri p0 p1 p2) :
    triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC ∧
    triProb p0 p1 p2 triPatSep = starProb (1 - p0) (1 - p1) (1 - p2) starPatSep ∧
    triProb p0 p1 p2 triPatAB = starProb (1 - p0) (1 - p1) (1 - p2) starPatAB ∧
    triProb p0 p1 p2 triPatAC = starProb (1 - p0) (1 - p1) (1 - p2) starPatAC ∧
    triProb p0 p1 p2 triPatBC = starProb (1 - p0) (1 - p1) (1 - p2) starPatBC :=
  ⟨stt_ABC p0 p1 p2 h, stt_Sep p0 p1 p2 h, stt_AB p0 p1 p2, stt_AC p0 p1 p2,
    stt_BC p0 p1 p2⟩


theorem isCriticalTri_of_starTriangle (p0 p1 p2 : ℝ)
    (h : triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC) :
    IsCriticalTri p0 p1 p2 := by
  have := stt_ABC_sub p0 p1 p2
  rw [h, sub_self] at this
  exact this.symm


theorem starTriangle_iff_isCriticalTri (p0 p1 p2 : ℝ) :
    (triProb p0 p1 p2 triPatABC = starProb (1 - p0) (1 - p1) (1 - p2) starPatABC) ↔
      IsCriticalTri p0 p1 p2 :=
  ⟨isCriticalTri_of_starTriangle p0 p1 p2, stt_ABC p0 p1 p2⟩


theorem bernoulliMeasure_map_not (p : ℝ≥0) (hp : p ≤ 1) :
    Measure.map (fun b => !b) (bernoulliMeasure p hp)
      = bernoulliMeasure (1 - p) tsub_le_self := by
  have hmeas : Measurable (fun b : Bool => !b) := measurable_of_countable _
  refine (MeasureTheory.Measure.ext_iff_singleton).2 ?_
  intro x
  rw [Measure.map_apply hmeas (measurableSet_singleton x)]
  cases x with
  | false =>
    have hpre : (fun b => !b) ⁻¹' ({false} : Set Bool) = ({true} : Set Bool) := by
      ext b; cases b <;> simp
    have harith : (1 : ℝ≥0) - (1 - p) = p := by
      apply NNReal.coe_injective
      rw [NNReal.coe_sub tsub_le_self, NNReal.coe_sub hp]; ring
    rw [bernoulliMeasure_apply_false, harith, hpre, bernoulliMeasure_apply_true]
  | true =>
    have hpre : (fun b => !b) ⁻¹' ({true} : Set Bool) = ({false} : Set Bool) := by
      ext b; cases b <;> simp
    rw [bernoulliMeasure_apply_true, hpre, bernoulliMeasure_apply_false,
      ENNReal.coe_sub, ENNReal.coe_one]


theorem one_sub_half : (1 : ℝ≥0) - 2⁻¹ = 2⁻¹ := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sub (by norm_num)]; push_cast; norm_num


theorem half_le_one : (2 : ℝ≥0)⁻¹ ≤ 1 := by
  rw [inv_le_one₀ (by norm_num)]; norm_num


theorem bernoulli_selfDual_half :
    Measure.map (fun b => !b) (bernoulliMeasure 2⁻¹ half_le_one)
      = bernoulliMeasure 2⁻¹ half_le_one := by
  rw [bernoulliMeasure_map_not]
  congr 1
  exact one_sub_half


theorem primal_open_iff_dual_closed (ω : ConfigSpace (Sym2 (Lattice.Site 2)))
    (e : Sym2 (Lattice.Site 2)) :
    ω e = true ↔ Lattice.dualConfig ω (Lattice.crossEdge e) = false :=
  Lattice.isOpen_iff_dual_isClosed ω e

end Universality
end StatMech
