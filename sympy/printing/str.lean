import sympy.core.expr
import stdlib.Lean.Name
import stdlib.Lean.Level
import stdlib.List
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

def Expr.strFormat : Expr → String
  | nil => ""

  | const _
  | sort _
  | Symbol .. =>
    "%s"

  | Basic func args =>
    let opStr := func.operator
    match func with
    | .BinaryInfix ⟨op⟩ =>
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
        | `Membership.mem
        | `List.Mem
        | _ =>
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
      | _ =>
        opStr

    | .UnaryPrefix ⟨op⟩ =>
      if let [arg] := args then
        let arg :=
          if func.priority > arg.priority then
            "(%s)"
          else
            "%s"
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
        | .L_forall =>
          match args with
          | [_, Binder .given _ _ nil] =>
            "%s → %s"
          | [expr, _] =>
            if expr.is_Propositional then
              -- α → Prop
              "%s → %s"
            else
              ""
          | _ =>
            ""
        | .L_lambda =>
          opStr ++ " %s".repeat (args.length - 1) ++ " ↦ %s"
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
      | .L_function _
      | .L_operatorname _ =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "(%s)"
          else
            "%s"
        s!"{opStr} " ++ " ".intercalate args
      | .LMethod name idx =>
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
          if let obj :: args := args.swap 0 idx then
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
      | .L_typeclass _ =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "(%s)"
          else
            "%s"
        let args := " ".intercalate args
        s!"{opStr} {args}"
      | .LProperty name =>
        match args with
        | arg :: _ =>
          let arg :=
            if func.priority > arg.priority then
              "(%s)"
            else
              "%s"
          s!"{arg}{opStr}"
        | .nil =>
          name.toString

  | Binder binder binderName _ value =>
    let binderName := binderName.escape_specials " "
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
    [name.normalized.toString]

  | Basic func args =>
    match func with
    | .ExprWithLimits op =>
      let args' :=
        match op with
        | .L_forall =>
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
          | [returnType, Binder .given _ binderType nil] =>
            [binderType.toString, returnType.toString]
          | _ =>
            []
        | .L_lambda =>
          match args with
          | expr :: limits =>
            let limits := limits.map fun arg =>
              match arg with
              | Binder .default name _ nil =>
                name.toString
              | _ =>
                arg.toString
            limits.reverse ++ [expr.toString]
          | .nil =>
            []
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
    | .ExprWithAttr (.LMethod _ idx) =>
      map (args.swap 0 idx)
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
