module

public import Theorem.List.Permute__Neg.eq.Append_AppendRotateDropTake
public import Theorem.Nat.EqMin.of.Lt
public import Theorem.Nat.LtAdd.of.Lt_Sub
public import Theorem.List.ProdAppend.eq.MulProdS
public import Theorem.Nat.MinAddS.eq.AddMin
public import Theorem.Nat.Val.lt.Sub_1.of.Val.ne.Sub_1

public import Theorem.Bool.UFn.of.Eq
public import Theorem.List.AppendAppend.eq.Append_Append
public section

open List Bool Nat Int


public theorem List.ProdPermute__Neg.eq.MulProd_ProdDrop
  [Monoid α]
  {s : List α}
-- given
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.permute i (-d : ℤ)).prod = ((s.take (i + 1)).take ((s.take (i + 1)).length - (d + 1)) ++ ((s.take (i + 1)).drop ((s.take (i + 1)).length - (d + 1))).rotate ((d + 1) ⊓ (s.take (i + 1)).length - 1)).prod * (s.drop (i + 1)).prod := by
-- proof
  rw [Permute__Neg.eq.Append_AppendRotateDropTake]
  simp_all
  repeat rw [MulProdS.eq.ProdAppend]
  apply UFn.of.Eq _ List.prod
  rw [Append_Append.eq.AppendAppend]


-- created on 2025-07-14
