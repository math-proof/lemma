module

public import Theorem.List.Permute.eq.Append_AppendRotateTakeDrop
public import Theorem.List.ProdAppend.eq.MulProdS

public section

open List


public theorem List.ProdPermute.eq.MulProd_ProdAppend
  [Monoid α]
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i d).prod = (s.take i).prod * (((s.drop i).take (d + 1)).rotate 1 ++ (s.drop i).drop (d + 1)).prod := by
-- proof
  simp_all [Permute.eq.Append_AppendRotateTakeDrop]


-- created on 2025-07-14
