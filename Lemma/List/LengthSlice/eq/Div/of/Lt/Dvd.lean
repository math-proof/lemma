import Lemma.List.EqLengthSlice_CoeMul.of.Lt
import Lemma.Nat.Any_Eq_Mul.of.Dvd
import Lemma.Nat.EqDivMul.of.Ne_0
import stdlib.Slice
open Nat List


@[main]
private lemma main
  {d n : ℕ}
-- given
  (h_d : d ∣ n)
  (h_i : i < d) :
-- imply
  (⟨i, n, d⟩ : Slice).length n = n / d := by
-- proof
  let ⟨m, h_n⟩ := Any_Eq_Mul.of.Dvd.left h_d
  subst h_n
  rw [EqDivMul.of.Ne_0 (by omega)]
  rwa [EqLengthSlice_CoeMul.of.Lt]


-- created on 2025-11-14
