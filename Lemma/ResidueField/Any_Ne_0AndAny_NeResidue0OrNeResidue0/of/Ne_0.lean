import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.RegularProlongation
import Lemma.Int.P2MUtil

open AlgebraicCurve IsLocalRing

/--
[AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_RegularProlongation_exists_smul_mem_integers_and_residue_ne_zero_or.lean)
-/
@[path]
private lemma main
  [Field L] [Field F] [Algebra L F] [Field Fbar]
  {A : ValuationSubring L} [Algebra (IsLocalRing.ResidueField ↥A) Fbar]
  {R₁ R₂ : AlgebraicCurve.RegularProlongation A F Fbar}
  {f : F}
-- given
  (hf : f ≠ 0) :
-- imply
  ∃ c : L, c ≠ 0 ∧ ∃ (h₁ : c • f ∈ R₁.integers) (h₂ : c • f ∈ R₂.integers),
      R₁.residue ⟨c • f, h₁⟩ ≠ 0 ∨ R₂.residue ⟨c • f, h₂⟩ ≠ 0 := by
  obtain ⟨c₁, h₁, hr₁⟩ := R₁.exists_smul_mem f hf
  obtain ⟨c₂, h₂, hr₂⟩ := R₂.exists_smul_mem f hf
  have hc₁ : c₁ ≠ 0 := R₁.smul_const_ne_zero h₁ hr₁
  have hc₂ : c₂ ≠ 0 := R₂.smul_const_ne_zero h₂ hr₂
  rcases A.mem_or_inv_mem (c₁ / c₂) with h | h
  ·
    have e : c₁ • f = algebraMap L F (c₁ / c₂) * (c₂ • f) := by
-- proof
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      congr 2
      field_simp
    have h₁₂ : c₁ • f ∈ R₂.integers := by
      rw [e]
      exact mul_mem ((R₂.algebraMap_mem_iff _).mpr h) h₂
    exact ⟨c₁, hc₁, h₁, h₁₂, Or.inl hr₁⟩
  ·
    rw [inv_div] at h
    have e : c₂ • f = algebraMap L F (c₂ / c₁) * (c₁ • f) := by
      rw [Algebra.smul_def, Algebra.smul_def, ← mul_assoc, ← map_mul]
      congr 2
      field_simp
    have h₂₁ : c₂ • f ∈ R₁.integers := by
      rw [e]
      exact mul_mem ((R₁.algebraMap_mem_iff _).mpr h) h₁
    exact ⟨c₂, hc₂, h₂₁, h₂, Or.inr hr₂⟩


-- created on 2026-10-23
