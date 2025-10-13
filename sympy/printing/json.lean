import sympy.parsing.parser
import sympy.printing.latex
import stdlib.Lean.Json
import stdlib.Array
open Lean.Meta
open Lean (Name Json getConstInfoInduct)

def Expr.collect (expr : Expr) (obj : Json) : Json :=
  match expr with
  | Binder binder .. =>
    let attr := binder.toString
    let list := obj.getObjValD attr
    let list :=
      match list with
      | .null =>
        #[]
      | .arr elems =>
        elems
      | _ =>
        panic! "unexpected JSON object"

    let new :=
      if attr == "given" then
        Json.mkObj ([
          ("lean", expr.toString),
          ("latex",
            (
              match expr with
              | Binder _ binderName binderType _ =>
                binderType.latex_tagged binderName
              | e =>
                panic! s!"{e}"
            )
          )
        ])
      else
        expr.toString
    obj.setObjVal! attr (Json.arr (list.unshift new))
  | _ =>
    Json.null


def Expr.toJson (this : Expr) : Json :=
  match this with
  | nil =>
    .null

  | Basic (.ExprWithLimits .Lean_forall) (expr :: limits) _ =>
    let codeObject := limits.foldl (fun obj limit => limit.collect obj) (Json.mkObj ([]))
    let imply := Json.mkObj ([
      ("lean", expr.toString),
      ("latex", expr.toLatex)
    ])
    codeObject.setObjVal! "imply" imply

  | Basic (.BinaryInfix op) .. =>
    if op.isProp then
      let imply := Json.mkObj ([
        ("lean", this.toString),
        ("latex", this.toLatex)
      ])
      Json.mkObj ([
        ("imply", imply),
      ])
    else
      .null

  | this =>
    this.toString


def Name.toJson (name : Name) : MetaM Json := do
  let type ← name.toExpr
  let expr ← Expr.toExpr type [] 0
  let mut json := expr.toJson.setObjVal! "name" name.toString
  json := json.setObjVal! "type" (← ppExpr type).pretty
  for attr in (← getConstInfoInduct `Lean.BinderInfo).ctors do
    let attr := attr.getLast.toString
    let value := json.getObjValD attr
    match value with
    | .null =>
      continue
    | .arr elems =>
      let elems := elems.map Json.getStr!
      let code := "\n".intercalate elems.toList
      json := json.setObjVal! attr code
    | _ =>
      panic! "unexpected JSON object"
  return json


#eval show MetaM Unit from do
  let ctors := (← getConstInfoInduct `Lean.BinderInfo).ctors
  for ctor in ctors do
    let ctor := ctor.getLast
    let ctor := ctor.toString
    IO.println ctor
