import Lemma.Algebra.Eq_AddMulDiv___Mod
import Lemma.Algebra.EqDivS.of.Eq
import Lemma.Nat.EqCoeS.is.Eq
import Lemma.Algebra.Div.eq.FloorDiv
import Lemma.Algebra.DivAdd.eq.AddDivS
import Lemma.Algebra.Ne_0
import Lemma.Algebra.NeCoeS.of.Ne
import Lemma.Algebra.EqDivMul.of.Ne_0
import Lemma.Nat.FloorAdd.eq.Add_Floor
import Lemma.Algebra.FloorDiv.eq.Zero
import Lemma.Algebra.FloorDivMod.eq.Zero
open Algebra Nat


@[main]
private lemma main
  {k n m : ℕ}
  {i : Fin m}
  {j : Fin n}
-- given
  (h_eq : k = i * n + j) :
-- imply
  i = k / n := by
-- proof
  have := Eq_AddMulDiv___Mod k n
  have := h_eq.symm.trans this
  have h_div := EqDivS.of.Eq this n
  have h_div := EqCoeS.of.Eq (R := ℤ) h_div
  repeat rw [Div.eq.FloorDiv] at h_div
  simp at h_div
  rw [DivAdd.eq.AddDivS] at h_div
  have h_n := Ne_0 j
  have h_n := NeCoeS.of.Ne.nat (R := ℚ) h_n
  rw [EqDivMul.of.Ne_0 h_n] at h_div
  rw [FloorAdd.eq.Add_Floor] at h_div
  rw [FloorDiv.eq.Zero] at h_div
  simp at h_div
  rw [DivAdd.eq.AddDivS] at h_div
  rw [EqDivMul.of.Ne_0 h_n] at h_div
  rw [FloorAdd.eq.Add_Floor] at h_div
  rw [FloorDivMod.eq.Zero] at h_div
  simp at h_div
  norm_cast at h_div


-- created on 2025-07-07
