import Lemma.Algebra.GetAdd.eq.AddGetS
open Algebra


@[main]
private lemma main
  [Add α]
-- given
  (h : i < n)
  (a b : List.Vector α n) :
-- imply
  (a + b)[i] = a[i] + b[i] := by
-- proof
  let i' : Fin n := ⟨i, h⟩
  have h_i : i' = i := rfl
  have := GetAdd.eq.AddGetS a b i'
  simp_all


-- created on 2025-07-20
