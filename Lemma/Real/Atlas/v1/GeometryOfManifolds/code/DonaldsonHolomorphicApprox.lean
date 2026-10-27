import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.GeometryOfManifolds.code.DonaldsonHolomorphicApprox
open Real MeasureTheory


/--
[donaldson_holomorphic_approximation_exp_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/DonaldsonHolomorphicApprox.lean)
-/
@[path]
lemma donaldson_holomorphic_approximation_exp_bound
  {n : ℕ}
  {D : CompactKahlerData n}
  {wcr : WeightedCrNorm D}
  {l2 : L2Norm D}
  {dol : DelbarOp D}
  {fam : SectionFamily D}
-- given
  (h_delbar_decay : ∃ (C_delbar lam_delbar : ℝ), C_delbar > 0 ∧ lam_delbar > 0 ∧ ∀ (k : ℕ) (p : D.M), l2.l2 (dol.delbar (fam.section_ k p)) ≤ C_delbar * exp (-lam_delbar * (k : ℝ) / 3))
  (h_green : ∃ (fam' : SectionFamily D), (∀ (k : ℕ) (p : D.M), dol.delbar (fam'.section_ k p) = 0) ∧ (∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧ ∀ (k : ℕ) (p : D.M), wcr.wnorm k r (fun q => fam.section_ k p q - fam'.section_ k p q) ≤ C_r * l2.l2 (dol.delbar (fam.section_ k p)))) :
-- imply
  ∃ (fam' : SectionFamily D), (∀ (k : ℕ) (p : D.M), dol.delbar (fam'.section_ k p) = 0) ∧ (∃ (lam : ℝ), lam > 0 ∧ ∀ (r : ℕ), ∃ (C_r : ℝ), C_r > 0 ∧ ∀ (k : ℕ) (p : D.M), wcr.wnorm k r (fun q => fam.section_ k p q - fam'.section_ k p q) ≤ C_r * exp (-lam * (k : ℝ) / 3)) := by
-- proof
  have _hkahler := D.kahler_compat
  have _hintegral := D.integrality_condition
  obtain ⟨fam', h_hol, h_cr_bound⟩ := h_green
  obtain ⟨C_d, lam_d, hCd_pos, hlam_pos, h_decay⟩ := h_delbar_decay
  refine ⟨fam', h_hol, lam_d, hlam_pos, fun r => ?_⟩
  obtain ⟨C_r, hCr_pos, h_wr_bound⟩ := h_cr_bound r
  refine ⟨C_r * C_d, by positivity, fun k p => ?_⟩
  calc wcr.wnorm k r (fun q => fam.section_ k p q - fam'.section_ k p q)
    ≤ C_r * l2.l2 (dol.delbar (fam.section_ k p)) := h_wr_bound k p
    _ ≤ C_r * (C_d * exp (-lam_d * (k : ℝ) / 3)) := by
      apply mul_le_mul_of_nonneg_left (h_decay k p) (le_of_lt hCr_pos)
    _ = C_r * C_d * exp (-lam_d * (k : ℝ) / 3) := by ring


-- created on 2026-10-23
