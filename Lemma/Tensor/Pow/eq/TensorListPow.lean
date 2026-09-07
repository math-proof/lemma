import Lemma.Tensor.Eq.is.EqDataS
import sympy.tensor.tensor
open Tensor


@[main]
private lemma main
  [Monoid α]
-- given
  (a : α)
  (n : ℕ) :
-- imply
  (a : Tensor α []) ^ n = ⟨[a ^ n], by simp⟩ := by
-- proof
  let a0 : Tensor α [] := a
  apply Eq.of.EqDataS
  apply Subtype.ext
  show (a0 ^ n).data.val = [a ^ n]
  induction n with
  | zero =>
    simp [pow_zero]
    rfl
  | succ m ih =>
    rw [pow_succ]
    simp [HMul.hMul, Mul.mul]
    cases hL : (a0 ^ m).data with
    | mk xs hxs =>
      cases hR : a0.data with
      | mk ys hys =>
        simp
        have hxs' : xs = [a ^ m] := by
          have := ih
          rw [hL] at this
          exact this
        have hys' : ys = [a] := by
          have : a0.data.val = [a] := rfl
          rw [hR] at this
          exact this
        simp [hxs', hys']
        simp [List.Vector.map₂, List.zipWith]
        exact (pow_succ a m).symm


-- created on 2026-09-07
