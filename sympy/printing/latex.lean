import stdlib.Lean.Level
import stdlib.Lean.Name
import stdlib.List
import sympy.core.expr
open Lean (Name)


def Expr.is_Div : Expr → Bool
  | Basic (.BinaryInfix ⟨`HDiv.hDiv⟩) _ => true
  | _ => false


def Expr.is_Mem : Expr → Bool
  | Basic (.BinaryInfix ⟨op⟩) args =>
    match op with
    | `Membership.mem
    | `List.Mem => args.length == 2
    | _ => false
  | _ => false


def Expr.is_Bool : Expr → Bool
  | Basic (.Special ⟨`Bool.toNat⟩) args => args.length == 1
  | _ => false


def Expr.is_Card : Expr → Bool
  | Basic (.Special ⟨`Finset.card⟩) args => args.length == 1
  | _ => false


def Expr.is_Abs : Expr → Bool
  | Basic (.Special ⟨`abs⟩) args => args.length == 1
  | _ => false


def Expr.countCases : Expr → Nat
  | Basic (.Special ⟨`ite⟩) args =>
    match args with
    | [_, _, elseBranch] => elseBranch.countCases + 1
    | _ => 1
  | _ => 0


def Expr.latexFormat : Expr → String
  | nil => ""
  | const _
  | sort _
  | Symbol .. => "%s"

  | e@(Basic func args) =>
    let opStr := func.command
    match func with
    | .BinaryInfix ⟨op⟩ =>
      match args with
      | [left, right] =>
        match op with
        | `HDiv.hDiv
        | `Rat.divInt =>
          if left.is_Div then
            "\\left. %s \\right/ %s"
          else
            s!"{opStr} %s %s"

        | `FloorDiv =>
          "%s {/\\!\\!/} %s"

        | `HPow.hPow =>
          let left :=
            if func.priority ≤ left.priority || left.is_Abs || left.is_Bool || left.is_Card then
              "%s"
            else
              "{\\left(%s\\right)}"
          s!"{left} {opStr} %s"
        | `And
        | `Or =>
          -- right associative operators
          let left :=
            if func.priority ≥ left.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          let right :=
            if func.priority > right.priority then
              "{\\left(%s\\right)}"
            else
              "%s"

          s!"{left} {opStr} {right}"
        | _ =>
          -- left associative operators
          let left :=
            if func.priority ≤ left.priority || left.is_Abs || left.is_Bool || left.is_Card then
              "%s"
            else
              "{\\left(%s\\right)}"
          let right :=
            if func.priority < right.priority || right.is_Div then
              "%s"
            else
              "{\\left(%s\\right)}"

          s!"{left} {opStr} {right}"
      | _ =>
        op.toString

    | .UnaryPrefix ⟨op⟩ =>
      if let [arg] := args then
        let format :=
          match op with
          | `Not =>
            if arg.is_Mem then
              "%s \\notin %s"
            else
              ""
          | `Real.sqrt
          | `Root.sqrt =>
            s!"{opStr}%s"
          | _ =>
            ""
        if format.isEmpty then
          let arg :=
            if func.priority > arg.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          s!"{opStr}{arg}"
        else
          format
      else
        op.toString

    | .UnaryPostfix ⟨op⟩ =>
      if let [arg] := args then
        let arg :=
          if func.priority > arg.priority then
            "{\\left(%s\\right)}"
          else
            "%s"
        s!"{arg}{opStr}"
      else
        op.toString

    | .ExprWithLimits op =>
      let opStr' :=
        match op with
        | .L_forall =>
          match args with
          | [Symbol _ (sort (.succ _)), _] =>
            "%s \\rightarrow %s"
          | [_, Binder .given _ type nil] =>
            match type with
            | Basic (.BinaryInfix ⟨`Membership.mem⟩) _ => ""
            | _ => "%s \\rightarrow %s"
          | _ => ""
        | .L_lambda =>
          opStr ++ "\\ %s".repeat (args.length - 1) ++ "\\mapsto\\ %s"
        | .L_sum
        | .L_prod =>
          opStr ++ "\\limits_{\\substack{%s}} {%s}"
        | _ =>
          ""
      if opStr' == "" then
        opStr ++ "\\ %s".repeat (args.length - 1) ++ ",\\ %s"
      else
        opStr'

    | .Special ⟨op⟩ =>
      match op with
      | .anonymous =>
        -- similar like Python' list.enumerate
        let args := args.zipIdx.map fun ⟨arg, i⟩ =>
          if i > 0 && arg.priority ≤ func.priority || i == 0 && arg.priority < func.priority then
            "{\\left(%s\\right)}"
          else
            "%s"
        "\\ ".intercalate args
      | `ite =>
        "\\begin{cases} %s \\\\ {%%s} & {\\color{blue}\\text{else}} \\end{cases}".format "\\\\".implode (List.replicate e.countCases "%s")
      | `Insert.insert =>
        "\\left\\{%s, %s\\right\\}"
      | `List.get
      | `List.Vector.get
      | `GetElem.getElem =>
        match args with
        | list :: _ :: _ =>
          let list :=
            if func.priority < list.priority || list.is_Abs || list.is_Bool || list.is_Card then
              "%s"
            else
              "{\\left(%s\\right)}"
          s!"{list}_%s"
        | _ =>
          opStr
      | `GetElem?.getElem? =>
        match args with
        | list :: _ =>
          let list :=
            if func.priority < list.priority || list.is_Abs || list.is_Bool || list.is_Card then
              "%s"
            else
              "{\\left(%s\\right)}"
          let index := "{%s?}"
          s!"{list}_{index}"
        | _ =>
          opStr
      | _ =>
        opStr
    | .ExprWithAttr op =>
      match op with
      | .L_function _ =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "\\left(%s\\right)"
          else
            "%s"
        opStr ++ "\\ " ++ "\\ ".intercalate args
      | .L_operatorname name =>
        match name with
        | `Real.exp => "{\\color{RoyalBlue} e} ^ %s"
        | `Set.Ioo => "\\left(%s, %s\\right)"
        | `Set.Ico => "\\left[%s, %s\\right)"
        | `Set.Iio => "\\left(-\\infty, %s\\right]"
        | `Set.Icc => "\\left[%s, %s\\right]"
        | `Set.Iic => "\\left(-\\infty, %s\\right]"
        | `Set.Ioc => "\\left(%s, %s\\right]"
        | `Set.Ici => "\\left[%s, \\infty\\right)"
        | `Set.Ioi => "\\left(%s, \\infty\\right)"
        | `Zeros => "\\mathbf{0}_{%s}"
        | `Ones => "\\mathbf{1}_{%s}"
        | _  =>
          let args := args.map fun arg =>
            if func.priority ≥ arg.priority then
              "\\left(%s\\right)"
            else
              "%s"
          opStr ++ "\\ " ++ "\\ ".intercalate args
      | .LMethod name idx =>
        let attr := name.getLast.toString.escape_specials
        match attr, args with
        | "ediv", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left :=
            if func.priority > left.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          let right :=
            if func.priority ≥ right.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          s!"{left} \\div {right}"
        | "fdiv", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left :=
            if func.priority > left.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          let right :=
            if func.priority ≥ right.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          s!"{left} /\\!\\!/ {right}"
        | "fmod", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left :=
            if func.priority ≥ left.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          let right :=
            if func.priority ≥ right.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          "%s \\textcolor{red}{\\%%%%} %s".format left, right
        | _, args =>
          if let obj :: args := args.swap 0 idx then
            let obj :=
              if func.priority ≥ obj.priority then
                "\\left(%s\\right)"
              else
                "%s"
            let args := args.map fun arg =>
              if func.priority > arg.priority then
                "\\left(%s\\right)"
              else
                "%s"
            let args := "\\ ".intercalate args
            s!"{obj}.{attr}\\ {args}"
          else
            opStr
      | .L_typeclass _ =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "\\left(%s\\right)"
          else
            "%s"
        let args := "\\ ".intercalate args
        s!"{opStr}\\ {args}"
      | .LProperty name =>
        let attr := name.getLast.toString
        match name with
        | `Complex.exp =>
          "{\\color{RoyalBlue} e} ^ %s"
        | `Complex.cos
        | `Complex.sin
        | `Complex.log =>
          s!"\\{attr} %s"
        | `IsConstant.is_constant =>
          "%s\\ {\\color{blue}\\text{is}}\\ {constant}"
        | _ =>
          match args with
          | arg :: _ =>
            let arg :=
              if func.priority > arg.priority then
                "{\\left(%s\\right)}"
              else
                "%s"
            s!"{arg}.{attr}"
          | .nil =>
            name.toString

  | Binder binder binderName _ value =>
    let binderName := binderName.escape_specials "\\ "
    match binder with
    | .instImplicit =>
      binder.func.command
    | .default =>
      if value == .nil then
        binder.func.command.replaceFirst "%s" binderName
      else
        s!"\\left({binderName} : %s := %s\\right)"
    | _ =>
      binder.func.command.replaceFirst "%s" binderName


partial def Expr.toLatex (e : Expr) : String :=
  e.latexFormat.printf (latexArgs e)
where
  latexArgs : Expr → List String
  | nil => []

  | const val =>
    [val.toLatex]

  | sort u =>
    [u.toString]

  | Symbol name _ =>
    [name.normalized.toString.escape_specials]

  | Basic func args =>
    match func with
    | .ExprWithLimits op =>
      let args' :=
        match op with
        | .L_forall =>
          match args with
          | [returnType@(Symbol _ (sort (.succ _))), Binder .default _ binderType nil]
          | [returnType, Binder .given _ binderType nil] =>
            [binderType.toLatex, returnType.toLatex]
          | _ =>
            []
        | .L_lambda =>
          match args with
          | expr :: limits =>
            let limits := limits.map fun arg =>
              match arg with
              | Binder .default name _ nil =>
                name.toString.escape_specials
              | _ =>
                arg.toLatex
            limits.reverse ++ [expr.toLatex]
          | .nil =>
            []
        | .L_exists =>
          match args with
          | [expr, Binder .default name type nil] =>
            [("{%s : %s}".format name.toString, type.toLatex), expr.toLatex]
          | _ =>
            []
        | _ =>
          []
      if args' == [] then
        map args |>.reverse
      else
        args'
    | .Special ⟨op⟩ =>
      match op with
      | `Nat.ModEq =>
        match args with
        | [d, a, b] =>
          [a.toLatex, b.toLatex, d.toLatex]
        | _ =>
          map args
      | `ite =>
        merge_ite e []
      | `Insert.insert =>
        match args with
        | [a, Basic (.Special ⟨`Singleton.singleton⟩) [b]] =>
          [a.toLatex, b.toLatex]
        | [a, .Symbol b _] =>
          [a.toLatex, "..." ++ b.toString]
        | _ =>
          map args
      | _ =>
        map args
    | .BinaryInfix ⟨`Membership.mem⟩ =>
      map args |>.reverse
    | .ExprWithAttr (.LMethod _ idx) =>
      map (args.swap 0 idx)
    | .UnaryPrefix ⟨`Not⟩ =>
      match args with
      | [arg] =>
        if arg.is_Mem then
          latexArgs arg
        else
          map args
      | _ =>
        map args
    | _ =>
      map args

  | Binder _ _ binderType value =>
    if value == nil then
      [binderType.toLatex]
    else
      [binderType.toLatex, value.toLatex]

  map : List Expr → List String
  | [] => []
  | head :: tail => ("{%s}".format head.toLatex) :: map tail

  merge_ite : Expr → List String → List String
  | Basic (.Special ⟨`ite⟩) args, cases =>
    match args with
    | [ifBranch, thenBranch, elseBranch] =>
      let ifBranch :=
        match ifBranch with
        | Binder .given name type nil =>
          "{%s} : {%s}".format name.toString, type.toLatex
        | _ =>
          ifBranch.toLatex
      let cases := cases.concat ("{{%s}} & {\\color{blue}\\text{if}}\\ %s ".format thenBranch.toLatex, ifBranch)
      merge_ite elseBranch cases
    | _=>
      cases
  | e, cases =>
    cases.concat e.toLatex


def Expr.latex_tagged (expr : Expr) (hypId : Name) (color : String := "green") : String :=
  "%s\\tag*{$\\color{%s}%s$}".format expr.toLatex, color, (hypId.escape_specials ".")
