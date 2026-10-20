import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma exists_pred_le_of_nonneg_of_ne_zero
  {r p : ℕ} (hp : 1 ≤ p)
  {n n' : Fin (r + 1) → ℕ} {a : Fin (r + 1) → ℤ}
  (hprof : ∀ i : Fin (r + 1), (n' i : ℤ) = p * a i + (n i : ℤ) - a (i + 1))
  (hpos : ∀ i, 0 ≤ a i) (hne : ∃ i, a i ≠ 0) :
  -- imply
  ∃ i, (p : ℤ) - 1 ≤ (n' i : ℤ) := by
  -- proof
  obtain ⟨i, -, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin (r + 1))) a ⟨0, Finset.mem_univ 0⟩
  refine ⟨i, ?_⟩
  obtain ⟨j, hj⟩ := hne
  have hj1 : 1 ≤ a j := lt_of_le_of_ne (hpos j) (Ne.symm hj)
  have hi1 : 1 ≤ a i := le_trans hj1 (hmax j (Finset.mem_univ j))
  have hsucc : a (i + 1) ≤ a i := hmax (i + 1) (Finset.mem_univ (i + 1))
  have h4 := hprof i
  have hni : (0 : ℤ) ≤ (n i : ℤ) := Int.natCast_nonneg _
  have hp1 : (1 : ℤ) ≤ (p : ℤ) := by
    exact_mod_cast hp
  have hfactor : ((p : ℤ) - 1) * 1 ≤ ((p : ℤ) - 1) * a i := mul_le_mul_of_nonneg_left hi1 (by omega)
  have hexp : ((p : ℤ) - 1) * a i = (p : ℤ) * a i - a i := by
    ring
  rw [mul_one, hexp] at hfactor
  omega

/--
[HopfAlgebra_Raynaud_valProfile_eq_zero_of_ramification_lt](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_Raynaud_valProfile_eq_zero_of_ramification_lt.lean)
-/
@[path]
private lemma main
  {r p e : ℕ} (hpe : e + 1 < p)
  {n n' : Fin (r + 1) → ℕ} {a : Fin (r + 1) → ℤ}
  (hprof : ∀ i : Fin (r + 1), (n' i : ℤ) = p * a i + (n i : ℤ) - a (i + 1))
  (hpos : ∀ i, 0 ≤ a i) (hbound : ∀ i, n' i ≤ e) :
  -- imply
  ∀ i, a i = 0 := by
  -- proof
  intro i
  by_contra hne0
  have hp1 : 1 ≤ p := by
    omega
  obtain ⟨j, hj⟩ := exists_pred_le_of_nonneg_of_ne_zero hp1 hprof hpos ⟨i, hne0⟩
  have hb : (n' j : ℤ) ≤ (e : ℤ) := by
    exact_mod_cast hbound j
  have hep : (e : ℤ) + 1 < (p : ℤ) := by
    exact_mod_cast hpe
  omega


-- created on 2026-10-20
