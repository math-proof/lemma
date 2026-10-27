import Initialize.Lean.Meta.CtorName
import Def.Data.String.String.Part2
import Instance.Lean.ConstantInfo.Part4


def Lean.ConstantInfo.proof (info : ConstantInfo) : Expr :=
  info.value! (allowOpaque := true)

