import stdlib.Basic
import stdlib.String
open Lean

def Lean.Name.head (name : Name) : Name :=
  name.components.headD default

def Lean.Name.get (name : Name) (i : Nat): Name :=
  name.components.getD i default

def Lean.Name.getLast (name : Name) : Name :=
  match name with
  | str _ s => s.toName
  | _ => default

def Lean.Name.dropLast (name : Name) : Name :=
  match name with
  | str pre _
  | num pre _ => pre
  | _ => default

def Lean.Name.normalized (name : Name) : List String :=
  if name == default then
    ["⊢"]
  else
    let components := name.components
    if let some (.succ index) := components.idxOf? `«_@» then
      if h : index < components.length then
        (components.take index).map Name.toString ++ [components[index].toString ++ "✝"]
      else
        components.map Name.toString
    else
      components.map Name.toString

def Lean.Name.escape_specials (name : Name) (sep : String) : String :=
  sep.intercalate (name.normalized.map .escape_specials)

def Lean.Name.toConstantInfo (name : Name) : MetaM ConstantInfo := do
  -- Check if the constant exists in the environment
  if (← getEnv).contains name then
    getConstInfo name
  else
    throwError s!"Constant {name} not found"

def Lean.Name.toExpr (name : Name) : MetaM Expr := do
  (·.type) <$> name.toConstantInfo
  -- name.toConstantInfo >>= fun info => return info.type

def Lean.Name.projFieldName (typeName : Name) (idx : Nat) : MetaM Name := do
  let some info := Lean.getStructureInfo? (← getEnv) typeName  | throwError s!"Declaration {typeName} not found"
  let fieldName := info.fieldNames[idx]!
  return str typeName fieldName.toString

def Lean.Name.suffix : Name → Name
  | str prev name =>
    str (prev.suffix) name.toLower
  | _ =>
    default

def Lean.Name.lemmaName (path : Name) (declName : Name) : Name :=
  let suffix := declName.suffix
  if suffix == `main then
    path
  else
    path ++ suffix

#eval mkCtorName ``Lean.Name
