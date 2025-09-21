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

def Expr.is_GetElem : Expr → Bool
  | Basic (.Special ⟨`GetElem.getElem⟩) args => args.length == 3
  | Basic (.Special ⟨op⟩) args =>
    match op with
    | `List.get
    | `List.Vector.get
    | `Tensor.get =>
      args.length == 2
    | _ =>
      false
  | _ => false

def Expr.is_GetElem? : Expr → Bool
  | Basic (.Special ⟨`GetElem?.getElem?⟩) args => args.length == 2
  | _ => false

def Expr.is_LeanProperty : Expr → Bool
  | Basic (.ExprWithAttr (.LeanProperty name)) _ => name != `IsConstant.is_constant
  | _ => false

def Expr.toList : Expr → Option (List Expr)
  | Basic (.BinaryInfix ⟨`List.cons⟩) [head, tail] =>
    if let some args := tail.toList then
      head :: args
    else
      none
  | .const (.ident `List.nil) => some .nil
  | _ => none

def Expr.traceCases (e : Expr) : Nat × Expr :=
  match e with
  | Basic (.Special ⟨`ite⟩) args =>
    match args with
    | [_, _, elseBranch] =>
      let ⟨n, e⟩ := elseBranch.traceCases
      ⟨n + 1, e⟩
    | _ =>
      ⟨1, e⟩
  | _ =>
    ⟨0, e⟩


def BinaryInfix.latexFormat (op : BinaryInfix) (left right : Expr) : String :=
  let func := op.func
  let opStr := func.command
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


def Expr.latexFormat : Expr → String
  | nil => ""
  | const _
  | sort _
  | Symbol .. => "%s"

  | e@(Basic func args) =>
    let opStr := func.command
    match func with
    | .BinaryInfix binop@(⟨op⟩) =>
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
        | `List.cons =>
          if let some args := e.toList then
            let format := ", ".intercalate (["%s"].repeat args.length)
            s!"\\left[{format}\\right]"
          else
            binop.latexFormat left right
        | _ =>
          binop.latexFormat left right
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
          | `Neg.neg =>
            if let const (.ident `Hyperreal.epsilon) := arg then
              "0^-"
            else if arg.is_Div then
              s!"{opStr}%s"
            else
              ""
          | _ =>
            ""
        if format.isEmpty then
          let arg :=
            if func.priority > arg.priority then
              "{\\left(%s\\right)}"
            else
              "%s"
          let arg :=
            if func.priority == 76 then
              "\\ " ++ arg
            else
              arg
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
        | .Lean_forall =>
          match args with
          | [Symbol _ (sort (.succ _)), _] =>
            "%s \\rightarrow %s"
          | [_, Binder .given _ type nil] =>
            match type with
            | Basic (.BinaryInfix ⟨`Membership.mem⟩) _ => ""
            | _ => "%s \\rightarrow %s"
          | _ => ""
        | .Lean_lambda =>
          opStr ++ "\\ %s".repeat (args.length - 1) ++ "\\mapsto\\ %s"
        | .Lean_let =>
          "{\\begin{align*}" ++ ("\\\\".intercalate ([s!"&{opStr}\\ %s := ⋯"].repeat (args.length - 1))) ++ "\\\\&%s\\end{align*}}"
        | .Lean_sum
        | .Lean_prod
        | .Lean_bigcup
        | .Lean_bigcap =>
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
        let ⟨n, last⟩ := e.traceCases
        if last == .nil then
          "\\overbrace{\\begin{cases} %s \\end{cases}}^{\\color{blue}{match}}".format "\\\\".implode (["%s"].repeat n)
        else
          "\\begin{cases} %s \\\\ {%%s} & {\\color{blue}\\text{else}} \\end{cases}".format "\\\\".implode (["%s"].repeat n)
      | `Insert.insert =>
        "\\left\\{%s, %s\\right\\}"
      | `List.get
      | `List.Vector.get
      | `Tensor.get
      | `GetElem.getElem =>
        match args with
        | list :: _ =>
          let list :=
            if func.priority < list.priority || list.is_Abs || list.is_Bool || list.is_Card || list.is_GetElem || list.is_GetElem? || list.is_LeanProperty then
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
            if func.priority < list.priority || list.is_Abs || list.is_Bool || list.is_Card || list.is_GetElem || list.is_GetElem? || list.is_LeanProperty then
              "%s"
            else
              "{\\left(%s\\right)}"
          let index := "{%s?}"
          s!"{list}_{index}"
        | _ =>
          opStr
      | .str _ "mk" =>
        let args := ["%s"].repeat args.length
        let args := ", ".intercalate args
        s!"\\langle {args} \\rangle"
      | _ =>
        opStr
    | .ExprWithAttr op =>
      match op with
      | .Lean_function _ =>
        let args := args.map fun arg =>
          if func.priority ≥ arg.priority then
            "\\left(%s\\right)"
          else
            "%s"
        opStr ++ "\\ " ++ "\\ ".intercalate args
      | .Lean_operatorname name =>
        match name with
        | `Real.exp => "{\\color{RoyalBlue} e} ^ %s"
        | `Finset.Ioo
        | `Set.Ioo => "\\left(%s, %s\\right)"
        | `Finset.Ico
        | `Set.Ico => "\\left[%s, %s\\right)"
        | `Finset.Iio
        | `Set.Iio => "\\left(-\\infty, %s\\right]"
        | `Finset.Icc
        | `Set.Icc => "\\left[%s, %s\\right]"
        | `Finset.Iic
        | `Set.Iic => "\\left(-\\infty, %s\\right]"
        | `Finset.Ioc
        | `Set.Ioc => "\\left(%s, %s\\right]"
        | `Finset.Ici
        | `Set.Ici => "\\left[%s, \\infty\\right)"
        | `Finset.Ioi
        | `Set.Ioi => "\\left(%s, \\infty\\right)"
        | `Zeros => "\\mathbf{0}_{%s}"
        | `Ones => "\\mathbf{1}_{%s}"
        | `Stack =>
          let parentheses : Bool :=
            if let [_, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default _ _ nil]] := args then
              fn.priority < (⟨`List.cons⟩ : BinaryInfix).func.priority
            else
              false
          let arg := if parentheses then "{\\left(%s\\right)}" else "%s"
          s!"\\left[%s < %s\\right] {arg}"
        | `letFun => "{\\begin{align*}&{\\color{blue}{let}}\\ %s : %s := ⋯\\\\&%s\\end{align*}}"
        | `KroneckerDelta => "\\delta_{%s %s}"
        | `OfScientific.ofScientific => "%s%s.%s"
        | _  =>
          let args := args.map fun arg =>
            if func.priority ≥ arg.priority then
              "\\left(%s\\right)"
            else
              "%s"
          opStr ++ "\\ " ++ "\\ ".intercalate args
      | .LeanMethod name idx =>
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
        | "getSlice", [_, Basic (.Special ⟨`Slice.mk⟩) [start, _, step]] =>
          if let const (.natVal 1) := step then
            if let const (.natVal 0) := start then
              "{%s}_{:%s}"
            else
              "{%s}_{%s:%s}"
          else
            if let const (.natVal 0) := start then
              "{%s}_{:%s:%s}"
            else
              "{%s}_{%s:%s:%s}"
        | _, args =>
          if args.length ≤ idx then
            let op := name.toString.escape_specials
            let args := args.map fun arg =>
              if func.priority > arg.priority then
                "\\left(%s\\right)"
              else
                "%s"
            let args := "\\ ".intercalate args
            s!"{op}\\ {args}"
          else if let obj :: args := args.swap 0 idx then
            let obj :=
              if func.priority ≥ obj.priority && obj.toList == none then
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
      | .Lean_typeclass _ =>
        let args := args.map fun arg =>
          if arg.priority ≤ func.priority && arg.toList == none then
            "\\left(%s\\right)"
          else
            "%s"
        let args := "\\ ".intercalate args
        s!"{opStr}\\ {args}"
      | .LeanProperty name =>
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
        | `Tensor.T =>
          "{%s}^{\\color{magenta} T}"
        | _ =>
          match args with
          | arg :: _ =>
            let arg :=
              if func.priority > arg.priority && arg.toList == none then
                "{\\left(%s\\right)}"
              else
                "%s"
            s!"{arg}.{attr}"
          | .nil =>
            name.toString.escape_specials
      | .LeanLemma _ =>
        opStr

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
    [name.escape_specials "."]

  | Basic func args =>
    match func with
    | .ExprWithLimits op =>
      let args' :=
        match op with
        | .Lean_forall =>
          match args with
          | [returnType@(Symbol _ (sort (.succ _))), Binder .default _ binderType nil]
          | [returnType, Binder .given _ binderType nil] =>
            [binderType.toLatex, returnType.toLatex]
          | _ =>
            []
        | .Lean_lambda =>
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
        | .Lean_let =>
          args.reverse.map fun expr =>
            if let Binder _ name type _ := expr then
              "{%s : %s}".format name.toString.escape_specials, type.toLatex
            else
              "{%s}".format expr.toLatex
        | .Lean_exists
        | .Lean_sum
        | .Lean_prod
        | .Lean_bigcup
        | .Lean_bigcap =>
          match args with
          | [expr, Binder .default name type nil] =>
            [("{%s : %s}".format name.toString.escape_specials, type.toLatex), expr.toLatex]
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
      | `Fin.mk =>
        cdots args
      | _ =>
        map args
    | .BinaryInfix ⟨`Membership.mem⟩ =>
      map args |>.reverse
    | .BinaryInfix ⟨`List.cons⟩ =>
      if let some args := e.toList then
        map args
      else
        map args
    | .ExprWithAttr op =>
      match op with
      | .LeanMethod op idx =>
        match op with
        | .str _ "getSlice" =>
          if let [base, Basic (.Special ⟨`Slice.mk⟩) [start, stop, step]] := args then
            if let const (.natVal 1) := step then
              if let const (.natVal 0) := start then
                map [base, stop]
              else
                map [base, start, stop]
            else
              if let const (.natVal 0) := start then
                map [base, stop, step]
              else
                map [base, start, stop, step]
          else
            map args
        | _ =>
          map (args.swap 0 idx)
      | .Lean_operatorname `Stack =>
        if let [n, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default i _ nil]] := args then
          i.toString.escape_specials :: map [n, fn]
        else
          map args
      | .Lean_operatorname `letFun =>
        if let [_, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder _ h hType _]] := args then
          h.toString.escape_specials :: map [hType, fn]
        else
          map args
      | .Lean_operatorname `cast =>
        cdots args
      | .Lean_operatorname `OfScientific.ofScientific =>
        if let [mantissa, exponentSign, decimalExponent] := args then
          let mantissa :=
            if let const (.natVal mantissa) := mantissa then
              mantissa
            else
              0
          let decimalExponent :=
            if let const (.natVal decimalExponent) := decimalExponent then
              decimalExponent
            else
              0
          let pow10 := 10 ^ decimalExponent
          let integer := toString (mantissa / pow10)
          let fraction := toString (mantissa % pow10)
          let sign :=
            if let const .true := exponentSign then
              ""
            else
              "-"
          [sign, integer, fraction]
        else
          map args
      | .Lean_typeclass `HEq =>
        cdots args
      | _ =>
        map args
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

  cdots : List Expr → List String
  | [a, Basic (.ExprWithAttr _) _] =>
    map [a] ++ ["\\cdots"]
  | args@([a, Basic (.UnaryPrefix op) _]) =>
    if op.func.priority == 76 then
      map [a] ++ ["\\cdots"]
    else
      map args
  | [Basic (.ExprWithAttr _) _, a] =>
    "\\cdots" :: map [a]
  | args@([Basic (.UnaryPrefix op) _, a]) =>
    if op.func.priority == 76 then
      "\\cdots" :: map [a]
    else
      map args
  | args =>
    map args

  merge_ite : Expr → List String → List String
  | Basic (.Special ⟨`ite⟩) args, cases =>
    match args with
    | [ifBranch, thenBranch, elseBranch] =>
      let ifBranch :=
        match ifBranch with
        | Binder .given name type nil =>
          "{%s} : {%s}".format name.toString.escape_specials, type.toLatex
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
