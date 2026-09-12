import sympy.matrices.expressions.permutation
import Lemma.Nat.Delta.eq.Ite
open Nat


@[main]
private lemma main
-- given
  (i j : Fin n) :
-- imply
  ∑ x : Fin n, KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ) = 1 := by
-- proof
  rw [Fintype.sum_equiv i.addRight
      (fun x => KroneckerDelta ((x + i : Fin n) : ℕ) (j : ℕ))
      (fun y => KroneckerDelta (y : ℕ) (j : ℕ))
      (fun _ => rfl)]
  rw [Finset.sum_eq_single j]
  · simp [Nat.Delta.eq.Ite]
  · intro y _ hy
    simp only [Nat.Delta.eq.Ite]
    exact if_neg (fun hcon => hy (Fin.ext hcon))
  · intro hx
    exact False.elim (hx (Finset.mem_univ j))


-- created on 2026-09-12
