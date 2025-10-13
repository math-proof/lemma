import sympy.core.expr
import stdlib.Lean.Level
open Lean (FVarId Name)

def Expr.is_Propositional : Expr → Bool
  | Symbol _ (sort u) =>
    match u with
    | .param _
    | .succ _ =>
      true
    | _ =>
      false
  | sort u =>
    u == .zero
  | _ => false


def BinaryInfix.strFormat (op : BinaryInfix) (left right : Expr) : String :=
  let func := op.func
  let opStr := func.operator
  -- left associative operators
  let left :=
    if func.priority > left.priority then
      "(%s)"
    else
      "%s"
  let right :=
    if func.priority ≥ right.priority then
      "(%s)"
    else
      "%s"
  s!"{left} {opStr} {right}"

def List.swap0 (l : List α) (idx : Nat) : List α :=
  match idx with
  | 0 => l
  | .succ idx =>
     match l with
    | [] => []
    | head :: tail =>
      if let (middle, elemAtIdx :: tail) := tail.splitAt idx then
        elemAtIdx :: (middle ++ head :: tail)
      else
        l

def Expr.strFormat : Expr → String
  | nil => ""

  | const _
  | sort _
  | Symbol .. =>
    "%s"

  | Basic func args _ =>
    let opStr := func.operator
    match func with
    | .BinaryInfix binop@(⟨op⟩) =>
      match args with
      | [left, right] =>
        match op with
        | `And
        | `Or
        | `HPow.hPow =>
          let left :=
            -- right associative operators
            if func.priority ≥ left.priority then
              "(%s)"
            else
              "%s"
          let right :=
            if func.priority > right.priority then
              "(%s)"
            else
              "%s"
          s!"{left} {opStr} {right}"
        | `List.cons =>
          if let [_, .const (.ident `List.nil)] := args then
            s!"[%s]"
          else
            binop.strFormat left right
        | `Membership.mem
        | `List.Mem
        | _ =>
          binop.strFormat left right
      | _ =>
        opStr

    | .UnaryPrefix ⟨op⟩ =>
      if let [arg] := args then
        let arg :=
          if func.priority > arg.priority then
            "(%s)"
          else
            "%s"
        let arg :=
          if func.priority == 76 then
            -- UnaryPrefix resulted from Lean.Expr.proj
            " " ++ arg
          else
            arg
        s!"{opStr}{arg}"
      else
        op.toString

    | .UnaryPostfix _ =>
      match args with
      | [arg] =>
        let arg :=
          if func.priority > arg.priority then
            "(%s)"
          else
            "%s"
        s!"{arg}{opStr}"
      | _ =>
        s!"%s{opStr}"

    | .ExprWithLimits op =>
      let opStr' :=
        match op with
        | .Lean_forall =>
          match args with
          | [_, Binder .given _ _ nil]
          | [_, Binder .default _ _ nil] =>
            "%s → %s"
          | _ =>
            ""
        | .Lean_lambda =>
          opStr ++ " %s".repeat (args.length - 1) ++ " ↦ %s"
        | .Lean_let =>
          s!"{opStr} %s; ".repeat (args.length - 1) ++ "%s"
        | _ =>
          ""
      if opStr' == "" then
        opStr ++ " %s".repeat (args.length - 1) ++ ", %s"
      else
        opStr'

    | .Special ⟨op⟩ =>
      match op with
      | .anonymous =>
        let args := args.zipIdx.map fun ⟨arg, i⟩ =>
          if i > 0 && arg.priority ≤ func.priority || i == 0 && arg.priority < func.priority then
            "(%s)"
          else
            "%s"
        " ".intercalate args
      | `ite =>
        "if %s then %s else %s"
      | `Prod.mk
      | `abs
      | `Norm.norm
      | `List.get
      | `List.Vector.get
      | `GetElem.getElem
      | `Singleton.singleton
      | `setOf
      | _ =>
        opStr

    | .ExprWithAttr op =>
      match op with
      | .Lean_function _
      | .Lean_operatorname _ =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "(%s)"
          else
            "%s"
        s!"{opStr} " ++ " ".intercalate args
      | .LeanMethod name idx =>
        let attr := name.getLast.toString
        match attr, args with
        | "map", [fn, obj] =>
          let fn :=
            if func.priority ≥ fn.priority then
              "(%s)"
            else
              "%s"
          let obj :=
            if func.priority ≥ obj.priority then
              "(%s)"
            else
              "%s"
          s!"{obj}.{attr} {fn}"
        | _, args =>
          if args.length ≤ idx then
            let op := name.toString
            let args := args.map fun arg =>
              if func.priority > arg.priority then
                "(%s)"
              else
                "%s"
            let args := " ".intercalate args
            s!"{op} {args}"
          else if let obj :: args := args.swap0 idx then
            let obj :=
              if func.priority ≥ obj.priority then
                "(%s)"
              else
                "%s"
            let args := args.map fun arg =>
              if func.priority > arg.priority then
                "(%s)"
              else
                "%s"
            let args := " ".intercalate args
            s!"{obj}.{attr} {args}"
          else
            opStr
      | .Lean_typeclass _ =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "(%s)"
          else
            "%s"
        let args := " ".intercalate args
        s!"{opStr} {args}"
      | .LeanProperty name =>
        match args with
        | arg :: _ =>
          let arg :=
            if func.priority > arg.priority then
              if let .Basic (.BinaryInfix ⟨`List.cons⟩) [_, .const (.ident `List.nil)] _ := arg then
                "%s"
              else
                "(%s)"
            else
              "%s"
          s!"{arg}{opStr}"
        | .nil =>
          name.toString
      | .LeanLemma name =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "(%s)"
          else
            "%s"
        s!"{name} " ++ " ".intercalate args
        -- opStr

  | Binder binder binderName _ value =>
    let binderName := " ".intercalate (binderName.normalized)
    match binder with
    | .instImplicit =>
      binder.func.operator
    | .default =>
      if value == .nil then
        binder.func.operator.replaceFirst "%s" binderName
      else
        s!"({binderName} : %s := %s)"
    | _ =>
      binder.func.operator.replaceFirst "%s" binderName


partial def Expr.toString (e : Expr) : String :=
  e.strFormat.printf (strArgs e)
where
  strArgs : Expr → List String
  | nil => []

  | const val =>
    [val.toString]

  | sort u =>
    [u.toString]

  | Symbol name _ =>
    [".".intercalate name.normalized]

  | Basic func args _ =>
    match func with
    | .ExprWithLimits op =>
      let args' :=
        match op with
        | .Lean_forall =>
          match args with
          | [returnType@(Symbol _ (sort u)), Binder .default _ binderType nil] =>
            match u with
            | .succ _
            | .param _ =>
              [binderType.toString, returnType.toString]
            | _ =>
              []
          | [returnType@((sort .zero)), Binder .default name binderType nil] =>
            [" → ".intercalate (List.replicate name.components.length binderType.toString), returnType.toString]
          | [returnType, Binder .given _ binderType nil]
          | [returnType, Binder .default _ binderType nil] =>
            [binderType.toString, returnType.toString]
          | _ =>
            []
        | .Lean_lambda =>
          match args with
          | expr :: limits =>
            let limits := limits.map fun arg =>
              match arg with
              | Binder .default binderName _ nil =>
                " ".intercalate (binderName.normalized)
              | _ =>
                arg.toString
            limits.reverse ++ [expr.toString]
          | .nil =>
            []
        | .Lean_let =>
          args.reverse.map fun expr =>
            if let Binder _ name type value := expr then
              "%s : %s := %s".format name.toString, type.toString, value.toString
            else
              "%s".format expr.toString
        | _ =>
          []
      if args' == [] then
        map args |>.reverse
      else
        args'
    | .Special ⟨`Nat.ModEq⟩ =>
      match args with
      | [d, a, b] =>
        [a.toString, b.toString, d.toString]
      | _ =>
        map args
    | .BinaryInfix ⟨`Membership.mem⟩ =>
      map args |>.reverse
    | .ExprWithAttr (.LeanMethod _ idx) =>
      map (args.swap0 idx)
    | _ =>
      map args

  | Binder (binderType := binderType) .. =>
    [binderType.toString]

  map : List Expr → List String
  | [] => []
  | head :: tail => head.toString :: map tail

instance : ToString Expr where
  toString := Expr.toString

instance : ToString Operator where
  toString : Operator → String
  | op => op.operator

instance : ToString FVarId where
  toString : FVarId → String
  | id => id.name.toString
