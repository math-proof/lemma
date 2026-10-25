/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Order/ErdosSzekeres.lean -/

import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Theorem.Combinatorics.Order.ErdosSzekeres.Part2


namespace MathlibExt.Combinatorics.Order.ErdosSzekeres

/-- Length of the longest increasing subsequence ending at `p`. -/
noncomputable def incrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : ℕ :=
  ((Finset.range (N + 1)).filter (IsIncrEnd f p)).max'
    ⟨1, by
      have hN : 0 < N := by
        have h := p.isLt
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, fun _ => p, singleton_incr f p, rfl⟩⟩

/-- Length of the longest decreasing subsequence ending at `p`. -/
noncomputable def decrLen {N : ℕ} (f : Fin N → ℝ) (p : Fin N) : ℕ :=
  ((Finset.range (N + 1)).filter (IsDecrEnd f p)).max'
    ⟨1, by
      have hN : 0 < N := by
        have h := p.isLt
        omega
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, by omega, fun _ => p, singleton_decr f p, rfl⟩⟩

/-- Append `p` to a length-`k` map, yielding a length-`k+1` map. -/
def extendMap {N k : ℕ} (φ : Fin k → Fin N) (p : Fin N) : Fin (k + 1) → Fin N :=
  fun i => if h : i.val < k then φ ⟨i.val, h⟩ else p

end MathlibExt.Combinatorics.Order.ErdosSzekeres
