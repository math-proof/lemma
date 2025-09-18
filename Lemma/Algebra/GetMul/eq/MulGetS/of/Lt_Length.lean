import Lemma.Algebra.GetMul.eq.MulGetS
open Algebra


@[main]
private lemma main
  [Mul α]
-- given
  (h : i < n)
  (a b : List.Vector α n) :
-- imply
  (a * b)[i] = a[i] * b[i] := by
-- proof
  let i' : Fin n := ⟨i, h⟩
  have h_i : i' = i := rfl
  have := GetMul.eq.MulGetS a b i'
  simp_all


-- created on 2025-07-03
-- updated on 2025-07-14
