import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1
open List


@[main, comm]
private lemma main
  [Mul α] [One α]
  {s : List α}
-- given
  (h : i < s.length) :
-- imply
  (s.drop i).prod = s[i] * (s.drop (i + 1)).prod := by
-- proof
  let i' : Fin s.length := ⟨i, h⟩
  have h : i' = i := rfl
  have := ProdDrop.eq.Mul_ProdDrop_Add_1 i'
  simp_all


-- created on 2025-06-08
