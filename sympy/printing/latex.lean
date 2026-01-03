import stdlib.Lean.Level
import stdlib.Lean.Name
import stdlib.List
import sympy.core.expr
open Lean (Name)

/--
| index |   hex  | color|
| ----- | ------ | -----|
| 0     |"#999"| Gray |
| 1     |"#99f"| Blue |
| 2     |"#9f9"|Green |
| 3     |"#9ff"| Cyan |
| 4     |"#f99"| Red  |
| 5     |"#f9f"| Pink |
| 6     |"#ff9"|Yellow|
| 7     |"#fff"|White |
-/
def Nat.toColor (n : ℕ) (ignore : Bool) : String :=
  if ignore then
    "%s"
  else
    let n := (n + 1) &&& 7
    let b := ['9', 'f'][n &&& 1]!
    let n := n >>> 1
    let g := ['9', 'f'][n &&& 1]!
    let n := n >>> 1
    let r := ['9', 'f'][n &&& 1]!
    -- for katex
    -- s!"\\colorbox\u007b#{r}{g}{b}\u007d\u007b$\\left(%s\\right)$\u007d"
    -- for complex math
    s!"\\colorbox\u007b#{r}{g}{b}\u007d\u007b$\\mathord\u007b\\left(%s\\right)\u007d$\u007d"
    -- for mathjax
    -- s!"\\bbox[#{r}{g}{b}]\u007b\\left(%s\\right)\u007d"

def Expr.is_Div : Expr → Bool
  | Basic (.BinaryInfix ⟨op⟩) .. =>
    match op with
    | `Div.div
    | `HDiv.hDiv
    | `Rat.divInt =>
      true
    | _ =>
      false
  | _ => false


def Expr.is_Mem : Expr → Bool
  | Basic (.BinaryInfix ⟨op⟩) args _ =>
    match op with
    | `Membership.mem
    | `List.Mem => args.length == 2
    | _ => false
  | _ => false


def Expr.is_Bool : Expr → Bool
  | Basic (.Special ⟨`Bool.toNat⟩) args _ => args.length == 1
  | _ => false


def Expr.is_Card : Expr → Bool
  | Basic (.Special ⟨`Finset.card⟩) args _ => args.length == 1
  | _ => false


def Expr.is_Abs : Expr → Bool
  | Basic (.Special ⟨`abs⟩) args _ => args.length == 1
  | _ => false

def Expr.is_GetElem : Expr → Bool
  | Basic (.Special ⟨`GetElem.getElem⟩) args _ => args.length == 3
  | Basic (.Special ⟨op⟩) args _ =>
    match op with
    | `List.get
    | `List.Vector.get
    | `Tensor.get =>
      args.length == 2
    | _ =>
      false
  | _ => false

def Expr.is_GetElem? : Expr → Bool
  | Basic (.Special ⟨`GetElem?.getElem?⟩) args _ => args.length == 2
  | _ => false

def Expr.is_LeanProperty : Expr → Bool
  | Basic (.ExprWithAttr (.LeanProperty name)) .. => name != `IsConstant.is_constant
  | _ => false

def Expr.toList : Expr → Option (List Expr)
  | Basic (.BinaryInfix ⟨`List.cons⟩) [head, tail] _ =>
    if let some args := tail.toList then
      head :: args
    else
      none
  | .const (.ident `List.nil) => some .nil
  | _ => none

def Expr.traceCases (e : Expr) : ℕ × Expr :=
  match e with
  | Basic (.Special ⟨`ite⟩) args _ =>
    match args with
    | [_, _, elseBranch] =>
      let ⟨n, e⟩ := elseBranch.traceCases
      ⟨n + 1, e⟩
    | _ =>
      ⟨1, e⟩
  | _ =>
    ⟨0, e⟩


def BinaryInfix.latexFormat (op : BinaryInfix) (left right : Expr) (level : ℕ) : String :=
  let func := op.func
  let opStr := func.command
  -- left associative operators
  let left := level.toColor (left.priority ≥ func.priority || left.is_Abs || left.is_Bool || left.is_Card)
  let right := level.toColor (right.priority > func.priority || right.is_Div)
  s!"{left} {opStr} {right}"


def Expr.latexFormat : Expr → String
  | nil => ""
  | const _
  | sort _
  | Symbol .. => "%s"

  | e@(Basic func args level) =>
    let opStr := func.command
    match func with
    | .BinaryInfix binop@(⟨op⟩) =>
      match args with
      | [left, right] =>
        match op with
        | `Div.div
        | `HDiv.hDiv
        | `Rat.divInt =>
          if left.is_Div then
            "\\left. %s \\right/ %s"
          else
            s!"{opStr} %s %s"

        | `FloorDiv =>
          "%s {/\\!\\!/} %s"

        | `HPow.hPow =>
          let left := level.toColor (left.priority ≥ func.priority || left.is_Abs || left.is_Bool || left.is_Card)
          s!"{left} {opStr} %s"
        | `And
        | `Or =>
          -- right associative operators
          let left := level.toColor (left.priority > func.priority)
          let right := level.toColor (right.priority ≥ func.priority)
          s!"{left} {opStr} {right}"
        | `List.cons =>
          if let some args := e.toList then
            let format := ", ".intercalate (["%s"].repeat args.length)
            s!"\\left[{format}\\right]"
          else
            binop.latexFormat left right level
        | _ =>
          binop.latexFormat left right level
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
          let arg := level.toColor (arg.priority ≥ func.priority)
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
        let arg := level.toColor (arg.priority ≥ func.priority)
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
            | Basic (.BinaryInfix ⟨`Membership.mem⟩) .. => ""
            | _ => "%s \\rightarrow %s"
          | _ =>
            ""
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
          level.toColor ((i == 0 || arg.priority > func.priority) && (i > 0 || arg.priority ≥ func.priority))
        "\\ ".intercalate args
      | `ite =>
        let ⟨n, last⟩ := e.traceCases
        if last == .nil then
          "\\overbrace{\\begin{cases} %s \\end{cases}}^{\\color{blue}match}".format "\\\\".implode (["%s"].repeat n)
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
          let list := level.toColor (list.priority > func.priority || list.is_Abs || list.is_Bool || list.is_Card || list.is_GetElem || list.is_GetElem? || list.is_LeanProperty)
          s!"{list}_%s"
        | _ =>
          opStr
      | `GetElem?.getElem? =>
        match args with
        | list :: _ =>
          let list := level.toColor (list.priority > func.priority || list.is_Abs || list.is_Bool || list.is_Card || list.is_GetElem || list.is_GetElem? || list.is_LeanProperty)
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
          level.toColor (arg.priority > func.priority)
        opStr ++ "\\ " ++ "\\ ".intercalate args
      | .Lean_operatorname name =>
        match name with
        | `Exp.exp
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
          let arg := level.toColor (
            if let [_, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default _ _ nil] _] := args then
              fn.priority ≥ (⟨`List.cons⟩ : BinaryInfix).func.priority
            else
              true
          )
          s!"\\left[%s < %s\\right] {arg}"
        | `letFun => "{\\begin{align*}&{\\color{blue}let}\\ %s : %s := ⋯\\\\&%s\\end{align*}}"
        | `KroneckerDelta => "\\delta_{%s %s}"
        | `OfScientific.ofScientific => "%s%s.%s"
        | `Subtype =>
          let postOp :=
            match args with
            -- consider special cases:
            | [Basic (.ExprWithLimits .Lean_lambda) [Basic (.BinaryInfix ⟨`LT.lt⟩) [const (.natVal 0), Symbol binderName binderType] _, Binder .default binderName' binderType' nil] _] =>
              -- ℝ⁺ = Subtype fun x : ℝ => 0 < x
              if binderName == binderName' && binderType == binderType' then
                "%s^{+}"
              else
                ""
            | [Basic (.ExprWithLimits .Lean_lambda) [Basic (.BinaryInfix ⟨`LT.lt⟩) [Symbol binderName binderType, const (.natVal 0)] _, Binder .default binderName' binderType' nil] _] =>
              -- ℝ⁻ = Subtype fun x : ℝ => x < 0
              if binderName == binderName' && binderType == binderType' then
                "%s^{-}"
              else
                ""
            | _ =>
              ""
          if postOp.isEmpty then
            let args := args.map fun arg =>
              level.toColor (arg.priority > func.priority)
            opStr ++ "\\ " ++ "\\ ".intercalate args
          else
            postOp
        | _  =>
          let args := args.map fun arg =>
            level.toColor (arg.priority > func.priority)
          opStr ++ "\\ " ++ "\\ ".intercalate args
      | .LeanMethod name idx =>
        let attr := name.getLast.toString.escape_specials
        match attr, args with
        | "ediv", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left := level.toColor (left.priority ≥ func.priority)
          let right := level.toColor (right.priority > func.priority)
          s!"{left} \\div {right}"
        | "fdiv", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left := level.toColor (left.priority ≥ func.priority)
          let right := level.toColor (right.priority > func.priority)
          s!"{left} /\\!\\!/ {right}"
        | "fmod", [left, right] =>
          let divOperator : BinaryInfix := ⟨`HDiv.hDiv⟩
          let func := divOperator.func
          let left := level.toColor (left.priority > func.priority)
          let right := level.toColor (right.priority > func.priority)
          "%s {\\color{red}\\%%%%} %s".format left, right
        | "getSlice", [_, Basic (.Special ⟨`Slice.mk⟩) [start, _, step] _] =>
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
              level.toColor (arg.priority ≥ func.priority)
            let args := "\\ ".intercalate args
            s!"{op}\\ {args}"
          else if let obj :: args := args.swap 0 idx then
            let obj := level.toColor (obj.priority > func.priority || obj.toList != none)
            let args := args.map fun arg =>
              level.toColor (arg.priority > func.priority)
            let args := "\\ ".intercalate args
            s!"{obj}.{attr}\\ {args}"
          else
            opStr
      | .Lean_typeclass _ =>
        let args := args.map fun arg =>
          level.toColor (arg.priority > func.priority || arg.toList != none)
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
            let arg := level.toColor (arg.priority ≥ func.priority || arg.toList != none)
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

  | Basic func args _ =>
    match func with
    | .ExprWithLimits op =>
      let args' :=
        match op with
        | .Lean_forall =>
          match args with
          | [returnType@(Symbol _ (sort (.succ _))), Binder .default _ binderType nil]
          | [returnType, Binder .given _ binderType nil] =>
            [binderType.toLatex, returnType.toLatex]
          | [scope, Binder .default binderName binderType nil] =>
            [("%s : %s".format (binderName.escape_specials "\\ "), binderType.toLatex), scope.toLatex]
          | _ =>
            []
        | .Lean_lambda =>
          match args with
          | expr :: limits =>
            let limits := limits.map fun arg =>
              match arg with
              | Binder .default name _ nil =>
                name.escape_specials "\\ "
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
        | [a, Basic (.Special ⟨`Singleton.singleton⟩) [b] _] =>
          [a.toLatex, b.toLatex]
        | [a, .Symbol b _] =>
          [a.toLatex, "..." ++ b.toString]
        | _ =>
          map args
      | `Subtype.mk
      | `Fin.mk =>
        let a : Option Expr :=
          match args with
          | [a, Basic op ..] =>
            match op with
            | .ExprWithAttr _
            | .ExprWithLimits .Lean_let =>
              a
            | .UnaryPrefix op =>
              if op.func.priority == 76 then
                a
              else
                none
            | _ =>
              none
          | _ =>
            none
        if let some a := a then
          map [a] ++ ["\\cdots"]
        else
          map args
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
          if let [base, Basic (.Special ⟨`Slice.mk⟩) [start, stop, step] _] := args then
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
        if let [n, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder .default i _ nil] _] := args then
          i.toString.escape_specials :: map [n, fn]
        else
          map args
      | .Lean_operatorname `letFun =>
        if let [_, Basic (.ExprWithLimits .Lean_lambda) [fn, Binder _ h hType _] _] := args then
          h.toString.escape_specials :: map [hType, fn]
        else
          map args
      | .Lean_operatorname `cast =>
        match args with
        | [Basic func .., a] =>
          match func with
          | .ExprWithAttr _
          | .Special ⟨.anonymous⟩ =>
            "\\cdots" :: map [a]
          | _ =>
            map args
        | args =>
          map args
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
      | .Lean_operatorname `Subtype =>
        let args :=
          match args with
          -- consider special cases:
          | [Basic (.ExprWithLimits .Lean_lambda) [Basic (.BinaryInfix ⟨`LT.lt⟩) [const (.natVal 0), Symbol binderName binderType] _, Binder .default binderName' binderType' nil] _] =>
            -- ℝ⁺ = Subtype fun x : ℝ => 0 < x
            if binderName == binderName' && binderType == binderType' then
              [binderType]
            else
              args
          | [Basic (.ExprWithLimits .Lean_lambda) [Basic (.BinaryInfix ⟨`LT.lt⟩) [Symbol binderName binderType, const (.natVal 0)] _, Binder .default binderName' binderType' nil] _] =>
            -- ℝ⁻ = Subtype fun x : ℝ => x < 0
            if binderName == binderName' && binderType == binderType' then
              [binderType]
            else
              args
          | _ =>
            args
        map args
      | .Lean_typeclass `HEq =>
        match args with
        | [a, Basic (.ExprWithAttr _) ..] =>
          map [a] ++ ["\\cdots"]
        | args@([a, Basic (.UnaryPrefix op) ..]) =>
          if op.func.priority == 76 then
            map [a] ++ ["\\cdots"]
          else
            map args
        | [Basic (.ExprWithAttr _) .., a] =>
          "\\cdots" :: map [a]
        | args@([Basic (.UnaryPrefix op) .., a]) =>
          if op.func.priority == 76 then
            "\\cdots" :: map [a]
          else
            map args
        | args =>
          map args
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

  merge_ite : Expr → List String → List String
  | Basic (.Special ⟨`ite⟩) args _, cases =>
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
