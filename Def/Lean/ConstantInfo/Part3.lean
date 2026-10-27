import Initialize.Lean.Meta.CtorName
import Def.Data.String.String.Part2
import Instance.Lean.ConstantInfo.Part2


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

