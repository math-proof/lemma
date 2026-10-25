/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/MeshPatternGeneratingFunction.lean -/


import Mathlib.Algebra.Polynomial.Basic
import Lemma.Finset.Enumerative.MeshPatternGeneratingFunction


namespace MetaMathlibExt

open Polynomial

example (P : ℕ → ℕ → ℕ[X]) (n k : ℕ) (hk : 0 < k) (hnk : k ≤ n)
    (hbase : P (k - 1) k = C (Nat.factorial (k - 1)))
    (hstep : ∀ m, k ≤ m → P m k = (X + C (m - 1)) * P (m - 1) k) :
    P n k = C (Nat.factorial (k - 1)) * ∏ i ∈ Finset.range (n - k + 1), (X + C (k - 1 + i)) := by
  have hC (j : ℕ) : C j = (j : ℕ[X]) := map_natCast C j
  simp only [hC] at hbase hstep ⊢
  exact meshPatternGeneratingFunction_eq_factorial_mul_prod_general P n k X hk hnk hbase hstep

example (n : ℕ) (hn : 1 ≤ n) : n.factorial = ∏ i ∈ Finset.range n, (1 + i) := by
  have := meshPatternGeneratingFunction_eq_factorial_mul_prod_general (fun m _ => m.factorial) n 1 1
    one_pos hn rfl fun m hm => by
      cases m with
      | zero => omega
      | succ j => simp [Nat.factorial_succ, add_comm]
  simpa [Nat.sub_add_cancel hn] using this

end MetaMathlibExt
