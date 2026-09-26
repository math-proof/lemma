import Lemma.Real.HasDerivAtMulPowAbs
open Real


@[main]
private lemma main
  {n : ℕ}
  {x : ℝ}
-- given
  (h : 2 ≤ n) :
-- imply
  HasDerivAt (fun x => |x| ^ n) (n * |x| ^ (n - 2) * x) x := by
-- proof
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hf : (fun x : ℝ => |x| ^ (m + 2)) = fun y => |y| ^ m * y * y := by
    funext y
    rw [pow_add, sq_abs]
    ring
  rw [hf]
  refine (HasDerivAtMulPowAbs.mul (hasDerivAt_id' x)).congr_deriv ?_
  simp only [Nat.add_sub_cancel]
  push_cast
  ring


-- created on 2026-09-26