module

public import Initialize.Lean.Meta.CtorName
public import Def.Data.String.String.Part2
public import Def.Lean.ConstantInfo
@[expose] public section

instance : ToString Lean.ConstantVal := ⟨Lean.ConstantVal.toString⟩


