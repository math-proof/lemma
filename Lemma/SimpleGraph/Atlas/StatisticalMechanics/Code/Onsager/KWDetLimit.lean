import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.KWDetLimit.Part2
open StatMech StatMech.Onsager


/--
[ons_turnRoot_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma ons_turnRoot_sq_eq :
-- imply
  ons_turnRoot ^ 2 = Complex.I := by
-- proof
  apply StatMech.Onsager.ons_turnRoot_sq

/--
[ons_spaceRoot_primitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma ons_spaceRoot_primitive_eq
  {L : ℕ}
-- given
  (hL : L ≠ 0) :
-- imply
  IsPrimitiveRoot (ons_spaceRoot L) L := by
-- proof
  apply StatMech.Onsager.ons_spaceRoot_primitive L hL

/--
[ons_spaceRoot_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma ons_spaceRoot_pow_eq
  {L m : ℕ} :
-- imply
  ons_spaceRoot L ^ m = Complex.exp (Complex.I * ((2 * Real.pi * m / L : ℝ) : ℂ)) := by
-- proof
  apply StatMech.Onsager.ons_spaceRoot_pow L m

/--
[ons_spaceRoot_pow_add_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma ons_spaceRoot_pow_add_inv_eq
  {L m : ℕ} :
-- imply
  ons_spaceRoot L ^ m + (ons_spaceRoot L ^ m)⁻¹ = 2 * (Real.cos (2 * Real.pi * m / L) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_spaceRoot_pow_add_inv L m

/--
[ons_KWmat_det_eq_symbolProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma ons_KWmat_det_eq_symbolProd_eq
  {L : ℕ}
  [NeZero L]
  [Fact (1 < L)]
  {β : ℝ} :
-- imply
  (1 - ons_KWmat L (Real.tanh β : ℂ) ons_turnRoot).det = ∏ j : ZMod L × ZMod L, (ons_symbolDispersion β (2 * Real.pi * j.1.val / L) (2 * Real.pi * j.2.val / L) : ℂ) := by
-- proof
  apply StatMech.Onsager.ons_KWmat_det_eq_symbolProd L β

/--
[log_abs_ons_KWmat_det_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma log_abs_ons_KWmat_det_eq_sum_eq
  {L : ℕ}
  [NeZero L]
  [Fact (1 < L)]
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  Real.log ‖(1 - ons_KWmat L (Real.tanh β : ℂ) ons_turnRoot).det‖ = ∑ j : ZMod L × ZMod L, Real.log (ons_symbolDispersion β (2 * Real.pi * j.1.val / L) (2 * Real.pi * j.2.val / L)) := by
-- proof
  apply StatMech.Onsager.log_abs_ons_KWmat_det_eq_sum L β hβ hcrit

/--
[sum_zmod_prod_eq_sum_range](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma sum_zmod_prod_eq_sum_range_eq
  {L : ℕ}
  [NeZero L]
  {F : ℕ → ℕ → ℝ} :
-- imply
  (∑ j : ZMod L × ZMod L, F j.1.val j.2.val) = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, F i j := by
-- proof
  apply StatMech.Onsager.sum_zmod_prod_eq_sum_range L F

/--
[ons_KWdet_density_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma ons_KWdet_density_tendsto_eq
  {β : ℝ}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  Filter.Tendsto (fun L : ℕ => if h : 2 < L then letI : Fact (2 < L) := ⟨h⟩ Real.log ‖(1 - ons_KWmat L (Real.tanh β : ℂ) ons_turnRoot).det‖ / (2 * (L : ℝ) ^ 2) else 0) Filter.atTop (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
-- proof
  apply StatMech.Onsager.ons_KWdet_density_tendsto β hβ hcrit

/--
[ons_spinDet_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma ons_spinDet_pos_eq
  {L : ℕ}
  {β : ℝ}
  {a b : Fin 2}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  0 < ons_spinDet L β a b := by
-- proof
  apply StatMech.Onsager.ons_spinDet_pos L β hβ hcrit a b

/--
[log_ons_spinDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma log_ons_spinDet_eq
  {L : ℕ}
  {β : ℝ}
  {a b : Fin 2}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  Real.log (ons_spinDet L β a b) = ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L, Real.log (ons_symbolDispersion β (2 * Real.pi * (i + (a.val : ℝ) / 2) / L) (2 * Real.pi * (j + (b.val : ℝ) / 2) / L)) := by
-- proof
  apply StatMech.Onsager.log_ons_spinDet L β hβ hcrit a b

/--
[ons_halfShift_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma ons_halfShift_mem_Icc_eq
  {a : Fin 2} :
-- imply
  (a.val : ℝ) / 2 ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply StatMech.Onsager.ons_halfShift_mem_Icc a

/--
[ons_spinDet_density_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/KWDetLimit.lean)
-/
@[path]
private lemma ons_spinDet_density_tendsto_eq
  {β : ℝ}
  {a b : Fin 2}
-- given
  (hβ : 0 ≤ β)
  (hcrit : β ≠ ons_betaC) :
-- imply
  Filter.Tendsto (fun L : ℕ => Real.log (ons_spinDet L β a b) / (2 * (L : ℝ) ^ 2)) Filter.atTop (nhds (ons_freeEnergyIntegral β - 2 * Real.log (Real.cosh β))) := by
-- proof
  apply StatMech.Onsager.ons_spinDet_density_tendsto β hβ hcrit a b


-- created on 2026-10-23
