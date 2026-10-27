import Initialize.Lean.Meta.CtorName
import Def.Data.String.String.Part2


#eval mkCtorName ``Lean.ConstantInfo


def Lean.ConstantVal.toString : Lean.ConstantVal → String
  | ⟨name, levelParams, type⟩ => "{%s}".format s!"
  name = {name},
  levelParams = {levelParams},
  type = {type}
"

