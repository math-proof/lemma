import Lemma.List.EqLengthSlice_Mul
import Lemma.List.LengthSlice.eq.Div.of.Lt.Dvd
import Lemma.Nat.AddMul.lt.Mul
import Lemma.Nat.Any_Eq_Mul.of.Dvd
import Lemma.Nat.LtAddMul.of.Lt.Lt_Div.Dvd
import Lemma.Vector.GetGetSlice.eq.Get
import sympy.vector.vector
open List Nat Vector


@[main, fin]
private lemma main
-- given
  (h_d : d ∣ n)
  (h_i : i < n / d)
  (h_j : j < d)
  (v : List.Vector α n):
-- imply
  v[j : n:d][i]'(by simp_all [LengthSlice.eq.Div.of.Lt.Dvd]) = v[i * d + j]'(LtAddMul.of.Lt.Lt_Div.Dvd h_d h_i h_j) := by
-- proof
  let ⟨m, h_n⟩ := Any_Eq_Mul.of.Dvd.left h_d
  subst h_n
  rw [EqDivMul.of.Ne_0 (by omega)] at h_i
  have := GetGetSlice.eq.Get v ⟨i, h_i⟩ ⟨j, h_j⟩
  aesop


@[main]
private lemma fin.fin
  {n d j: ℕ}
  {i : Fin ((⟨j, n, d⟩ : Slice).length n)}
-- given
  (h_d : d ∣ n)
  (h_i : i < n / d)
  (h_j : j < d)
  (v : List.Vector α n) :
-- imply
  (v.getSlice ⟨j, n, d⟩).get i = v.get ⟨i * d + j, LtAddMul.of.Lt.Lt_Div.Dvd h_d h_i h_j⟩ :=
-- proof
  main h_d h_i h_j v


-- created on 2025-11-14
