import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Nat.Any_Eq_Mul.of.Dvd
import Lemma.Nat.EqDivMul.of.Ne_0
open Nat


@[main]
private lemma main
  {n : ℕ}
-- given
  (h_n : n ∣ s)
  (h_i : i < s / n)
  (h_j : j < n) :
-- imply
  i * n + j < s := by
-- proof
  let ⟨m, h_s⟩ := Any_Eq_Mul.of.Dvd.left h_n
  subst h_s
  apply AddMul.lt.Mul.of.Lt.Lt _ h_j
  rwa [EqDivMul.of.Ne_0 (by omega)] at h_i


-- created on 2025-11-14
