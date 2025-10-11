import Lemma.List.ProdDrop.eq.Mul_ProdDrop_Add_1
open List


@[main, comm]
private lemma main
  [Mul α] [One α]
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  (v.drop i).prod = v[i] * (v.drop (i + 1)).prod := by
-- proof
  let i' : Fin v.length := ⟨i, h⟩
  have h : i' = i := rfl
  have := ProdDrop.eq.Mul_ProdDrop_Add_1 i'
  simp_all


-- created on 2025-06-08
