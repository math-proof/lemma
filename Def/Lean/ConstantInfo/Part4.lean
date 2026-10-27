import Initialize.Lean.Meta.CtorName
import Def.Data.String.String.Part2
import Instance.Lean.ConstantInfo.Part3


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

