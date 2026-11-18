module

public import Def.Data.Tensor.Defs
public import Def.Data.Tensor.Defs.Part2
public import Def.Data.Tensor.Resize
public import Def.Data.Tensor.Shape
public import Def.Data.Tensor.Sum
public import Def.Data.Tensor.Mean
public import Def.Data.Tensor.Bmm
public import Def.Data.Tensor.Prod
public import Def.Data.Tensor.Reshape
public import Def.Data.Tensor.Unsqueeze
public import Def.Data.Tensor.Repeat
public import Notation.Data.Tensor.Permute
public import Def.Data.Tensor.Item
public import Def.Data.Tensor.HStack
public import Theorem.List.HeadD.eq.Get_0.of.GtLength_0
public import Theorem.Tensor.GtLength_0.of.GtLength_0
public import Theorem.Tensor.Length.eq.Get_0.of.GtLength_0

@[expose] public section
open Bool Nat Int List Tensor


def Tensor.get (X : Tensor α s) (i : Fin X.length) : Tensor α s.tail :=
  have h_i := i.isLt
  have h_GtLength_0 := GtLength_0.of.GtLength_0 (X := X) (by linarith)
  have h_EqHeadD := HeadD.eq.Get_0.of.GtLength_0 h_GtLength_0 1
  have := (Length.eq.Get_0.of.GtLength_0 h_GtLength_0 X).symm
  X.toVector[i]

