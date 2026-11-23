module

public import Initialize.Lean.Meta.CtorName
public import Def.Data.String.String.Part2
public import Def.Lean.ConstantInfo.Part2
@[expose] public section

instance : ToString Lean.DefinitionVal := ⟨Lean.DefinitionVal.toString⟩

