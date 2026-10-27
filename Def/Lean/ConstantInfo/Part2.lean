import Initialize.Lean.Meta.CtorName
import Def.Data.String.String.Part2
import Instance.Lean.ConstantInfo


def Lean.AxiomVal.toString : Lean.AxiomVal → String
  | ⟨constantVal, isUnsafe⟩ => "{%s}".format s!"
  constantVal : {constantVal},
  isUnsafe : {isUnsafe}
"

#eval mkCtorName ``Lean.ReducibilityHints

#eval mkCtorName ``Lean.DefinitionSafety

def Lean.DefinitionVal.toString : Lean.DefinitionVal → String
  | ⟨constantVal, value, hints, safety, all⟩ => "{%s}".format s!"
  constantVal : {constantVal},
  value : {value},
  hints : {hints.ctorName},
  safety : {safety.ctorName},
  all : {all}
"

