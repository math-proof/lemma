import Lean
open Lean


def Lean.ConstructorVal.toJson (ctor : ConstructorVal) : Json :=
  Json.mkObj [
    ("name", ctor.name.toString),
    ("numParams", ctor.numParams),
    ("numFields", ctor.numFields),
    ("isUnsafe", ctor.isUnsafe)
  ]

