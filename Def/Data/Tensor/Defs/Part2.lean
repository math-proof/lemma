module

public import Structure.Data.Tensor.Defs
public import Def.Data.Vector.Basic.Part2
public import Theorem.List.ProdTake_1.eq.HeadD_1

@[expose] public section
open Bool Nat Int List Lean


def Tensor.toVector (X : Tensor α s) : List.Vector (Tensor α s.tail) (s.headD 1) :=
  cast (by rw [ProdTake_1.eq.HeadD_1]) ((X.data.splitAt 1).map fun v : List.Vector α (s.drop 1).prod => (⟨cast (by simp) v⟩ : Tensor α s.tail))

