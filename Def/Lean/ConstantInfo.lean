module

public import Initialize.Lean.Meta.CtorName
public import Def.Data.String.String.Part2

@[expose] public section


#eval mkCtorName ``Lean.ConstantInfo


def Lean.ConstantVal.toString : Lean.ConstantVal → String
  | ⟨name, levelParams, type⟩ => "{%s}".format s!"
  name = {name},
  levelParams = {levelParams},
  type = {type}
"

