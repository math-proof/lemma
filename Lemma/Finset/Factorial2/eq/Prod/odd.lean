import Lemma.Finset.Factorial2.eq.Prod
open Finset Nat
@[path]
private lemma main
  {n : ℕ}
  (h : n % 2 = 1) :
  n ‼ = ∏ i ∈ Finset.Icc 1 ((n + 1) / 2), (2 * i - 1) := by
  rcases Nat.odd_iff.mpr h with ⟨m, rfl⟩
  have hhalf : (2 * m + 1 + 1) / 2 = m + 1 := by omega
  rw [hhalf]
  have hdouble : ((m + 1) * 2 - 1) ‼ = ∏ i ∈ Finset.Ico 1 ((m + 1) + 1), (2 * i - 1) := by
    exact Factorial2.eq.Prod.double_odd
  have hico2 : Finset.Ico 1 ((m + 1) + 1) = Finset.Ico 1 (m + 2) := by
    ext x; simp; omega
  have h_eq1 : (m + 1) * 2 - 1 = 2 * m + 1 := by omega
  rw [h_eq1, hico2] at hdouble
  rw [hdouble]
  have hico : Finset.Ico 1 (m + 2) = Finset.Icc 1 (m + 1) := by
    ext x
    simp [Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [hico]
-- created on 2023-08-17
