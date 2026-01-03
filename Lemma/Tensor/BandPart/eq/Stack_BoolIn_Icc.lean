import sympy.Basic
import sympy.matrices.expressions.special


@[main]
private lemma main
  [NatCast α]
  [One α]
  [Zero α]
-- given
  (n l u : ℕ) :
-- imply
  (1 : Tensor α [n, n]).band_part l u = [i < n] [j < n] (((j - i : ℤ) ∈ Icc (-l : ℤ) u) : Bool) := by
-- proof
  unfold Tensor.band_part
  sorry


-- created on 2026-01-02
-- updated on 2026-01-03
