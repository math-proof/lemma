import Lemma.List.EqLengthSlice_Mul.of.Lt
import Lemma.Nat.AddMul.lt.Mul.of.Lt.Lt
import Lemma.Vector.GetGetSlice.eq.Get
open List Nat Vector


@[main, fin]
private lemma main
  {m' n' n'' j' : ℤ}
  {m n : ℕ}
  {j : Fin n}
-- given
  (h_m' : m' = m)
  (h_n'' : n'' = n)
  (h_n' : n' = n)
  (h_j' : j' = j)
  (v : List.Vector α (m * n))
  (i : Fin ((⟨j', m' * n', n''⟩ : Slice).length (m * n))) :
-- imply
  have h_i : i < m := by
    have h_i := i.isLt
    subst h_m' h_n'' h_n' h_j'
    simp [EqLengthSlice_Mul.of.Lt] at h_i
    assumption
  have h_ij := AddMul.lt.Mul.of.Lt.Lt h_i j.isLt
  v[j' : m' * n':n''][i] = v[i * n + j] := by
-- proof
  intro h_i h_ij
  have := GetGetSlice.eq.Get v ⟨i, h_i⟩ j
  aesop


-- created on 2026-04-23
