import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.RothAuxiliary
import Lemma.Polynomial.NatAbsCoeff.le.RothPolyL1
import Lemma.Polynomial.RothPolyL1Mul.le.MulRothSPolyL1
import Lemma.Polynomial.RothPolyL1_C.eq.NatAbs
import Lemma.Real.RothPolyL1_RothScaledPowerCoord.le.PowRothCoordinateBase.of.Le
import Lemma.Real.RothCoordinateBase.Gt_0
open MathlibExt.NumberTheory.RothAuxiliary
open Real Polynomial
set_option maxHeartbeats 800000


attribute [local instance] Matrix.seminormedAddCommGroup

private lemma rothTermDegree_le_h
  {m : ℕ}
  {r : Fin m → ℕ}
  (i j : RothBox r) :
  rothTermDegree i j ≤ ∑ h, r h := by
  unfold rothTermDegree
  gcongr with h
  exact (Nat.sub_le _ _).trans (Nat.le_of_lt_succ (j h).isLt)

private lemma rothAuxTerm_l1_le_h
  (α : ℝ)
  {m : ℕ}
  {r : Fin m → ℕ}
  (i j : RothBox r) :
  rothPolyL1 (rothAuxTerm α i j) ≤
    (2 * rothCoordinateBase α) ^ (∑ h, r h) := by
  let S := ∑ h, r h
  have hn : rothTermDegree i j ≤ S := rothTermDegree_le_h i j
  have hch : (∏ h, Nat.choose (j h) (i h)) ≤ 2 ^ S := calc
    _ ≤ ∏ h, 2 ^ (j h : ℕ) := by
      gcongr with h
      exact Nat.choose_le_two_pow (j h) (i h)
    _ ≤ ∏ h, 2 ^ r h := by
      gcongr with h
      exact Nat.le_of_lt_succ (j h).isLt
    _ = 2 ^ S := Finset.prod_pow_eq_pow_sum Finset.univ r 2
  calc
    _ ≤ rothPolyL1 (Polynomial.C (∏ h, (Nat.choose (j h) (i h) : ℤ))) *
          rothPolyL1 (rothScaledPowerCoord α S (rothTermDegree i j)) :=
      RothPolyL1Mul.le.MulRothSPolyL1 _ _
    _ = (∏ h, Nat.choose (j h) (i h)) *
        rothPolyL1 (rothScaledPowerCoord α S (rothTermDegree i j)) := by
      rw [RothPolyL1_C.eq.NatAbs]
      change Int.natAbsHom (∏ h, (Nat.choose (j h) (i h) : ℤ)) * _ = _
      rw [map_prod]
      simp only [Int.natAbsHom_apply, Int.natAbs_natCast]
    _ ≤ 2 ^ S * rothCoordinateBase α ^ S := by
      exact Nat.mul_le_mul hch
        (RothPolyL1_RothScaledPowerCoord.le.PowRothCoordinateBase.of.Le α hn)
    _ = (2 * rothCoordinateBase α) ^ S := by rw [mul_pow]

private lemma rothAuxMatrix_entry_natAbs_le_h
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
  (u : RothLowIndex r γ × Fin (rothIntegralPolynomial α).natDegree)
  (j : RothBox r) :
  ((rothAuxMatrix α r γ u j).natAbs : ℝ) ≤
    ((2 * rothCoordinateBase α) ^ (∑ h, r h) : ℕ) := by
  exact_mod_cast
    (NatAbsCoeff.le.RothPolyL1 (rothAuxTerm α u.1.1 j) u.2).trans
      (rothAuxTerm_l1_le_h α u.1.1 j)

private lemma ridout_old_row_h
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
  (i : RothLowIndex r γ)
  (k : Fin (rothIntegralPolynomial α).natDegree)
  (j : RothBox r) :
  rothRidoutAuxMatrix α r γ (i, k.castSucc.castSucc) j =
    rothAuxMatrix α r γ (i, k) j := by
  simp [rothRidoutAuxMatrix]

private lemma ridout_low_row_h
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
  (i : RothLowIndex r γ)
  (j : RothBox r) :
  rothRidoutAuxMatrix α r γ
    (i, (Fin.last (rothIntegralPolynomial α).natDegree).castSucc) j =
    if j = i.1 then 1 else 0 := by
  simp [rothRidoutAuxMatrix]

private lemma ridout_complement_row_h
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
  (i : RothLowIndex r γ)
  (j : RothBox r) :
  rothRidoutAuxMatrix α r γ
    (i, Fin.last ((rothIntegralPolynomial α).natDegree + 1)) j =
    if j = rothRidoutBoxComplement r i.1 then 1 else 0 := by
  simp [rothRidoutAuxMatrix]

private lemma ridout_entry_natAbs_le_h
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ)
  (u : RothLowIndex r γ × Fin ((rothIntegralPolynomial α).natDegree + 2))
  (j : RothBox r) :
  ((rothRidoutAuxMatrix α r γ u j).natAbs : ℝ) ≤
    ((2 * rothCoordinateBase α) ^ (∑ h, r h) : ℕ) := by
  let H := (2 * rothCoordinateBase α) ^ (∑ h, r h)
  have hHnat : 1 ≤ H := by
    apply one_le_pow₀
    have hB := RothCoordinateBase.Gt_0 α
    omega
  have hH : (1 : ℝ) ≤ H := by exact_mod_cast hHnat
  obtain ⟨i, u⟩ := u
  refine Fin.lastCases ?_ (fun v ↦ ?_) u
  ·
    rw [ridout_complement_row_h]
    split_ifs <;> simp_all [H]
  ·
    refine Fin.lastCases ?_ (fun k ↦ ?_) v
    ·
      rw [ridout_low_row_h]
      split_ifs <;> simp_all [H]
    ·
      rw [ridout_old_row_h]
      exact rothAuxMatrix_entry_natAbs_le_h α r γ (i, k) j

/--
[rothRidoutAuxMatrix_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  (α : ℝ)
  {m : ℕ}
  (r : Fin m → ℕ)
  (γ : ℝ) :
-- imply
  ‖rothRidoutAuxMatrix α r γ‖ ≤
    ((2 * rothCoordinateBase α) ^ (∑ h, r h) : ℕ) := by
-- proof
  rw [Matrix.norm_le_iff (by positivity)]
  intro u j
  rw [Int.norm_eq_abs, ← Int.cast_abs]
  rw [← Int.natCast_natAbs]
  exact_mod_cast ridout_entry_natAbs_le_h α r γ u j


-- created on 2026-10-21
