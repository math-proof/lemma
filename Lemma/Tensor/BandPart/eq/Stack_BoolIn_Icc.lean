import Lemma.Tensor.BandPart.eq.Stack_BoolAnd_Dvd
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
open Tensor


@[main]
private lemma main
  [AddMonoidWithOne α]
-- given
  (m n l u : ℕ) :
-- imply
  (1 : Tensor α [m, n]).band_part l u = [i < m] [j < n] (((j - i : ℤ) ∈ Icc (-l : ℤ) u) : Bool) := calc
-- proof
  _  = (1 : Tensor α [m, n]).band_part l u 1 := rfl
  _ = [i < m] [j < n] (((j - i : ℤ) ∈ Icc (-l : ℤ) u ∧ (1 : ℤ) ∣ (j - i : ℤ) + l) : Bool) := BandPart.eq.Stack_BoolAnd_Dvd m n l u 1
  _ = [i < m] [j < n] (((j - i : ℤ) ∈ Icc (-l : ℤ) u) : Bool) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    repeat rw [EqGetStack.fn.fin]
    apply Eq.of.All_EqGetS.fin
    intro j
    repeat rw [EqGetStack.fn.fin]
    by_cases h : (j - i : ℤ) ∈ Icc (-l : ℤ) u
    · simp [h]
    · simp [h]


-- created on 2026-01-02
-- updated on 2026-07-28
