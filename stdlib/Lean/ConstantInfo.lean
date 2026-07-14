import stdlib.Basic
import stdlib.String
#eval mkCtorName ``Lean.ConstantInfo


def Lean.ConstantVal.toString : Lean.ConstantVal → String
  | ⟨name, levelParams, type⟩ => "{%s}".format s!"
  name = {name},
  levelParams = {levelParams},
  type = {type}
"

instance : ToString Lean.ConstantVal := ⟨Lean.ConstantVal.toString⟩


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

instance : ToString Lean.DefinitionVal := ⟨Lean.DefinitionVal.toString⟩

def Lean.TheoremVal.toString : Lean.TheoremVal → String
  | ⟨constantVal, value, all⟩ => "{%s}".format s!"
  constantVal : {constantVal},
  value : {value},
  all : {all}
"


def Lean.OpaqueVal.toString : Lean.OpaqueVal → String
  | ⟨constantVal, value, isUnsafe, all⟩ => "{%s}".format s!"
  constantVal : {constantVal},
  value : {value},
  isUnsafe : {isUnsafe},
  all : {all}
"


#eval mkCtorName ``Lean.QuotKind

def Lean.QuotVal.toString : Lean.QuotVal → String
  | ⟨constantVal, kind⟩ => "{%s}".format s!"
  constantVal : {constantVal},
  kind : {kind.ctorName}
"


def Lean.InductiveVal.toString : Lean.InductiveVal → String
  | ⟨constantVal, numParams, numIndices, all, ctors, numNested, isRec, isUnsafe, isReflexive⟩ =>
    "{%s}".format s!"
  constantVal : {constantVal},
  numParams : {numParams},
  numIndices : {numIndices},
  all : {all},
  ctors : {ctors},
  numNested : {numNested},
  isRec : {isRec},
  isUnsafe : {isUnsafe},
  isReflexive : {isReflexive}
"

def Lean.RecursorRule.toString : Lean.RecursorRule → String
  | ⟨ctor, nfields, rhs⟩ => "{%s}".format s!"
  ctor : {ctor},
  nfields : {nfields},
  rhs : {rhs}
"

instance : ToString Lean.RecursorRule := ⟨Lean.RecursorRule.toString⟩

def Lean.RecursorVal.toString : Lean.RecursorVal → String
  | ⟨constantVal, all, numParams, numIndices, numMotives, numMinors, rules, k, isUnsafe⟩ =>
    "{%s}".format s!"
  constantVal : {constantVal},
  all : {all},
  numParams : {numParams},
  numIndices : {numIndices},
  numMotives : {numMotives},
  numMinors : {numMinors},
  rules : {rules},
  k : {k},
  isUnsafe :
  {isUnsafe}
"


def Lean.ConstantInfo.toString : Lean.ConstantInfo → String
  | .axiomInfo    val => val.toString
  | .defnInfo     val => val.toString
  | .thmInfo      val => val.toString
  | .opaqueInfo   val => val.toString
  | .quotInfo     val => val.toString
  | .inductInfo   val => val.toString
  | .ctorInfo     val => val.toString
  | .recInfo      val => val.toString

instance : ToString Lean.ConstantInfo := ⟨Lean.ConstantInfo.toString⟩

def Lean.ConstantInfo.proof (info : ConstantInfo) : Expr :=
  info.value! (allowOpaque := true)
