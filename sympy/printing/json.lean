import sympy.parsing.parser
import sympy.printing.latex
import stdlib.Lean.Json
import stdlib.Array
open Lean.Meta
open Lean (Name Json getConstInfoInduct)

/-- Naming / structure tree for lemma-path suggestion (const vs method vs …). -/
partial def Expr.toStructJson (this : Expr) : Json :=
  match this with
  | nil =>
    .null

  | const val =>
    Json.mkObj [
      ("kind", "const"),
      ("value", val.toString),
    ]

  | sort u =>
    Json.mkObj [
      ("kind", "sort"),
      ("level", s!"{u}"),
    ]

  | Symbol name type =>
    Json.mkObj [
      ("kind", "symbol"),
      ("name", name.toString),
      ("type", type.toStructJson),
    ]

  | Binder binder binderName binderType value =>
    Json.mkObj [
      ("kind", "binder"),
      ("binder", binder.toString),
      ("name", binderName.toString),
      ("type", binderType.toStructJson),
      ("value", value.toStructJson),
    ]

  | Basic (.ExprWithAttr (.LeanMethod name idx)) args _ =>
    Json.mkObj [
      ("kind", "method"),
      ("name", name.toString),
      ("idx", s!"{idx}"),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.ExprWithAttr (.LeanProperty name)) args _ =>
    Json.mkObj [
      ("kind", "property"),
      ("name", name.toString),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.ExprWithAttr (.Lean_function name)) args _ =>
    Json.mkObj [
      ("kind", "function"),
      ("name", name.toString),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.ExprWithAttr (.Lean_operatorname name)) args _ =>
    Json.mkObj [
      ("kind", "operatorname"),
      ("name", name.toString),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.ExprWithAttr (.Lean_typeclass name)) args _ =>
    Json.mkObj [
      ("kind", "typeclass"),
      ("name", name.toString),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.ExprWithAttr (.LeanLemma name)) args _ =>
    Json.mkObj [
      ("kind", "lemma"),
      ("name", name.toString),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.BinaryInfix op) args _ =>
    let kind : String :=
      match op.name with
      | `Eq => "eq"
      | `Ne => "ne"
      | `LT.lt => "lt"
      | `GT.gt => "gt"
      | `LE.le => "le"
      | `GE.ge => "ge"
      | `And => "and"
      | `Or => "or"
      | `Iff => "iff"
      | `List.cons => "cons"
      | `Membership.mem | `List.Mem => "mem"
      | _ =>
        if op.isProp then "prop_infix" else "infix"
    Json.mkObj [
      ("kind", kind),
      ("op", op.name.toString),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.ExprWithLimits .Lean_forall) (expr :: limits) _ =>
    Json.mkObj [
      ("kind", "forall"),
      ("body", expr.toStructJson),
      ("binders", Json.arr (limits.toArray.map Expr.toStructJson)),
    ]

  | Basic (.ExprWithLimits .Lean_exists) (expr :: limits) _ =>
    Json.mkObj [
      ("kind", "exists"),
      ("body", expr.toStructJson),
      ("binders", Json.arr (limits.toArray.map Expr.toStructJson)),
    ]

  | Basic (.ExprWithLimits .Lean_lambda) (expr :: limits) _ =>
    Json.mkObj [
      ("kind", "fun"),
      ("body", expr.toStructJson),
      ("binders", Json.arr (limits.toArray.map Expr.toStructJson)),
    ]

  | Basic (.ExprWithLimits op) args _ =>
    let opName : String :=
      match op with
      | .Lean_sum => "sum"
      | .Lean_tsum => "tsum"
      | .Lean_prod => "prod"
      | .Lean_int _ => "int"
      | .Lean_bigcap => "bigcap"
      | .Lean_bigcup => "bigcup"
      | .Lean_lim => "lim"
      | .Lean_sup _ => "sup"
      | .Lean_inf _ => "inf"
      | .Lean_max _ => "max"
      | .Lean_min _ => "min"
      | .Lean_forall => "forall"
      | .Lean_exists => "exists"
      | .Lean_lambda => "lambda"
      | .Lean_let => "let"
    Json.mkObj [
      ("kind", "limits"),
      ("op", opName),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.UnaryPrefix op) args _ =>
    Json.mkObj [
      ("kind", "prefix"),
      ("op", op.name.toString),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.UnaryPostfix op) args _ =>
    Json.mkObj [
      ("kind", "postfix"),
      ("op", op.name.toString),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]

  | Basic (.Special op) args _ =>
    Json.mkObj [
      ("kind", "special"),
      ("op", op.name.toString),
      ("args", Json.arr (args.toArray.map Expr.toStructJson)),
    ]


/-- Fold binders (`given` / `default` / …) into a JSON object of arrays. -/
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
          ),
          ("struct",
            (
              match expr with
              | Binder _ _ binderType _ =>
                binderType.toStructJson
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


/-- Top-level lemma JSON: binders + imply (lean / latex / struct). -/
def Expr.toJson (this : Expr) : Json :=
  match this with
  | nil =>
    .null

  | Basic (.ExprWithLimits .Lean_forall) (expr :: limits) _ =>
    let codeObject := limits.foldl (fun obj limit => limit.collect obj) (Json.mkObj [])
    let imply := Json.mkObj ([
      ("lean", expr.toString),
      ("latex", expr.toLatex),
      ("struct", expr.toStructJson),
    ])
    codeObject.setObjVal! "imply" imply

  | Basic (.BinaryInfix op) .. =>
    if op.isProp then
      let imply := Json.mkObj ([
        ("lean", this.toString),
        ("latex", this.toLatex),
        ("struct", this.toStructJson),
      ])
      Json.mkObj ([
        ("imply", imply),
      ])
    else
      .null

  | this =>
    -- Fallback: still expose a structure tree when possible
    Json.mkObj [
      ("imply", Json.mkObj [
        ("lean", this.toString),
        ("latex", this.toLatex),
        ("struct", this.toStructJson),
      ])
    ]


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
