module
public import Mathlib
public import Theorem.Fin.NatAbsRothAuxMatrix.le.PowMul2RothCoordinateBaseSum.of.RothBox
public import Theorem.Fin.RothRidoutAuxMatrix_CastSuccCastSucc.eq.RothAuxMatrix.of.RothBox.RothLowIndex
public import Theorem.Fin.RothRidoutAuxMatrix_CastSuccLastNatDegreeRothIntegralPolynomial.eq.Eq_1.of.RothBox
public import Theorem.Fin.RothRidoutAuxMatrix_LastAddNatDegreeRothIntegralPolynomial1.eq.Eq_RothRidoutBoxComplement1.of.RothBox
public import Theorem.Real.RothCoordinateBase.Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open Fin Real


public section

/--
[rothRidoutAuxMatrix_entry_natAbs_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private theorem main
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
-- given
  (u : RothLowIndex r γ × Fin ((rothIntegralPolynomial α).natDegree + 2))
  (j : RothBox r) :
-- imply
  ((rothRidoutAuxMatrix α r γ u j).natAbs : ℝ) ≤
    ((2 * rothCoordinateBase α) ^ (∑ h, r h) : ℕ) := by
-- proof
  let H := (2 * rothCoordinateBase α) ^ (∑ h, r h)
  have hHnat : 1 ≤ H := by
    apply one_le_pow₀
    have hB := RothCoordinateBase.Gt_0 α
    omega
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hHnat
  obtain ⟨i, u⟩ := u
  refine Fin.lastCases ?_ (fun v ↦ ?_) u
  ·
    rw [RothRidoutAuxMatrix_LastAddNatDegreeRothIntegralPolynomial1.eq.Eq_RothRidoutBoxComplement1.of.RothBox]
    split_ifs <;> simp_all [H]
  ·
    refine Fin.lastCases ?_ (fun k ↦ ?_) v
    ·
      rw [RothRidoutAuxMatrix_CastSuccLastNatDegreeRothIntegralPolynomial.eq.Eq_1.of.RothBox]
      split_ifs <;> simp_all [H]
    ·
      rw [RothRidoutAuxMatrix_CastSuccCastSucc.eq.RothAuxMatrix.of.RothBox.RothLowIndex]
      exact NatAbsRothAuxMatrix.le.PowMul2RothCoordinateBaseSum.of.RothBox α r γ (i, k) j


-- created on 2026-10-21
