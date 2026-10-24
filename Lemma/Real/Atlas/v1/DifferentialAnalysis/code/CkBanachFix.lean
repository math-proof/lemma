import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.DifferentialAnalysis.code.CkBanachFix
open Filter Topology Finset TestFunctions
open scoped ZeroAtInfty


namespace TestFunctions

/--
[ContDiffZeroAtInfty.bddAbove_range_norm_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
lemma ContDiffZeroAtInfty.bddAbove_range_norm_val
  {n : ℕ}
  {u : ContDiffZeroAtInfty n} :
-- imply
  BddAbove (Set.range (fun x => ‖u.toZeroAtInftyContinuousMap x‖)) :=
-- proof
  ⟨‖u.toZeroAtInftyContinuousMap.toBCF‖, by
    rintro _ ⟨x, rfl⟩; exact u.toZeroAtInftyContinuousMap.toBCF.norm_coe_le_norm x⟩

end TestFunctions

namespace TestFunctions

/--
[ContDiffZeroAtInfty.continuous_partialDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
lemma ContDiffZeroAtInfty.continuous_partialDeriv
  {n : ℕ}
  {u : ContDiffZeroAtInfty n}
  {j : Fin n} :
-- imply
  Continuous (fun x => fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)) := by
-- proof
  have hcont_fderiv : Continuous (fderiv ℝ (⇑u.toZeroAtInftyContinuousMap)) :=
    u.contDiff_one.continuous_fderiv (by norm_num)
  exact (ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single j 1)).continuous.comp hcont_fderiv

end TestFunctions

namespace TestFunctions

/--
[ContDiffZeroAtInfty.bddAbove_range_norm_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
lemma ContDiffZeroAtInfty.bddAbove_range_norm_deriv
  {n : ℕ}
  {u : ContDiffZeroAtInfty n}
  {j : Fin n} :
-- imply
  BddAbove (Set.range (fun x => ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖)) :=
-- proof
  ⟨‖(u.partialDerivC0 j).toBCF‖, by
    rintro _ ⟨x, rfl⟩; exact (u.partialDerivC0 j).toBCF.norm_coe_le_norm x⟩

end TestFunctions

namespace TestFunctions

/--
[ContDiffZeroAtInfty.norm_apply_le_iSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
lemma ContDiffZeroAtInfty.norm_apply_le_iSup
  {n : ℕ}
  {u : ContDiffZeroAtInfty n}
  (x) :
-- imply
  ‖u.toZeroAtInftyContinuousMap x‖ ≤ ⨆ y, ‖u.toZeroAtInftyContinuousMap y‖ :=
-- proof
  le_ciSup u.bddAbove_range_norm_val x

end TestFunctions

namespace TestFunctions

/--
[ContDiffZeroAtInfty.norm_deriv_apply_le_iSup](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
lemma ContDiffZeroAtInfty.norm_deriv_apply_le_iSup
  {n : ℕ}
  {u : ContDiffZeroAtInfty n}
  {j : Fin n}
  (x) :
-- imply
  ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) x (EuclideanSpace.single j 1)‖ ≤ ⨆ y, ‖fderiv ℝ (⇑u.toZeroAtInftyContinuousMap) y (EuclideanSpace.single j 1)‖ :=
-- proof
  le_ciSup (u.bddAbove_range_norm_deriv j) x

end TestFunctions

namespace TestFunctions

/--
[ContDiffZeroAtInfty.sub_partialDerivC0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
lemma ContDiffZeroAtInfty.sub_partialDerivC0
  {n : ℕ}
  {u v : ContDiffZeroAtInfty n}
  {j : Fin n} :
-- imply
  (u - v).partialDerivC0 j = u.partialDerivC0 j - v.partialDerivC0 j := by
-- proof
  ext x
  simp only [partialDerivC0, ZeroAtInftyContinuousMap.coe_mk,
    ZeroAtInftyContinuousMap.coe_sub, Pi.sub_apply]
  have hu := u.differentiable x
  have hv := v.differentiable x
  have : (⇑(u - v).toZeroAtInftyContinuousMap : _ → ℂ) =
    ⇑u.toZeroAtInftyContinuousMap - ⇑v.toZeroAtInftyContinuousMap := funext (fun _ => rfl)
  rw [this, fderiv_sub hu hv, ContinuousLinearMap.sub_apply]

end TestFunctions

namespace TestFunctions

/--
[ContDiffZeroAtInfty.c0_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
lemma ContDiffZeroAtInfty.c0_norm_le
  {n : ℕ}
  {f : ContDiffZeroAtInfty n} :
-- imply
  ‖f.toZeroAtInftyContinuousMap‖ ≤ ‖f‖ := by
-- proof
  rw [f.norm_def]
  have : ‖f.toZeroAtInftyContinuousMap‖ =
    ⨆ x, ‖f.toZeroAtInftyContinuousMap x‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_eq_iSup_norm]
    rfl
  rw [this]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun j _ =>
    Real.iSup_nonneg fun x => norm_nonneg _)

end TestFunctions

namespace TestFunctions

/--
[ContDiffZeroAtInfty.pd_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
lemma ContDiffZeroAtInfty.pd_norm_le
  {n : ℕ}
  {f : ContDiffZeroAtInfty n}
  {j : Fin n} :
-- imply
  ‖f.partialDerivC0 j‖ ≤ ‖f‖ := by
-- proof
  rw [f.norm_def]
  have hpd_norm : ‖f.partialDerivC0 j‖ =
    ⨆ x, ‖(f.partialDerivC0 j) x‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm,
      BoundedContinuousFunction.norm_eq_iSup_norm]
    rfl
  rw [hpd_norm]
  have h_nn : 0 ≤ ⨆ x, ‖f.toZeroAtInftyContinuousMap x‖ :=
    Real.iSup_nonneg fun x => norm_nonneg _
  calc ⨆ x, ‖(f.partialDerivC0 j) x‖
    ≤ ∑ i : Fin n, ⨆ x, ‖(f.partialDerivC0 i) x‖ :=
      Finset.single_le_sum (f := fun i => ⨆ x, ‖(f.partialDerivC0 i) x‖)
        (fun i _ => Real.iSup_nonneg fun x => norm_nonneg _) (Finset.mem_univ j)
    _ ≤ (⨆ x, ‖f.toZeroAtInftyContinuousMap x‖) +
      ∑ i : Fin n, ⨆ x, ‖(f.partialDerivC0 i) x‖ :=
      le_add_of_nonneg_left h_nn
    _ = (⨆ x, ‖f.toZeroAtInftyContinuousMap x‖) +
      ∑ i : Fin n, ⨆ x,
        ‖fderiv ℝ (⇑f.toZeroAtInftyContinuousMap) x (EuclideanSpace.single i 1)‖ := by
      congr 1
end TestFunctions
open scoped ZeroAtInfty
open Filter Topology Finset
/-- Reconstruct a `ContDiffZeroAtInfty` element from a sequence converging uniformly with its partial derivatives. -/


/--
[ContDiffZeroAtInfty.c1_norm_add_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
private lemma c1_norm_add_le_eq
  {n : ℕ}
  {u v : ContDiffZeroAtInfty n} :
-- imply
  ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
-- proof
  apply TestFunctions.ContDiffZeroAtInfty.c1_norm_add_le u v

/--
[ContDiffZeroAtInfty.c1_norm_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
private lemma c1_norm_smul_eq
  {n : ℕ}
  {c : ℂ}
  {u : ContDiffZeroAtInfty n} :
-- imply
  ‖c • u‖ = ‖c‖ * ‖u‖ := by
-- proof
  apply TestFunctions.ContDiffZeroAtInfty.c1_norm_smul c u

/--
[ContDiffZeroAtInfty.c1_norm_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
private lemma c1_norm_eq_zero_iff_eq
  {n : ℕ}
  {u : ContDiffZeroAtInfty n} :
-- imply
  ‖u‖ = 0 ↔ u = 0 := by
-- proof
  apply TestFunctions.ContDiffZeroAtInfty.c1_norm_eq_zero_iff u

/--
[ContDiffZeroAtInfty.normedSpaceCore](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/CkBanachFix.lean)
-/
@[path]
private lemma normedSpaceCore_eq
  {n : ℕ} :
-- imply
  NormedSpace.Core ℂ (ContDiffZeroAtInfty n) where norm_nonneg := by
-- proof
  apply TestFunctions.ContDiffZeroAtInfty.normedSpaceCore


-- created on 2026-10-23
