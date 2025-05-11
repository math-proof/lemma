import stdlib.Lean.Expr
import sympy.core.singleton
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


structure Func where
  priority : Nat
  -- lean operator
  operator : String
  -- latex command
  command : String
deriving BEq, Repr, Inhabited


structure BinaryInfix where
  name : Name
deriving BEq, Repr


def BinaryInfix.func : BinaryInfix → Func
  | ⟨name⟩ =>
    match name with
    -- relational operator
    | `Iff => ⟨21, "↔", "\\leftrightarrow"⟩  -- L_leftrightarrow
    | `Or => ⟨30, "∨", "\\lor"⟩  -- L_lor
    | `And => ⟨35, "∧", "\\land"⟩  -- L_land
    | `LE.le => ⟨51, "≤", "\\le"⟩  -- L_le
    | `GE.ge => ⟨51, "≥", "\\ge"⟩  -- L_ge
    | `LT.lt => ⟨51, "<", "<"⟩  -- L_lt
    | `GT.gt => ⟨51, ">", ">"⟩  -- L_gt
    | `Eq => ⟨51, "=", "="⟩  -- LEq
    | `Ne => ⟨51, "≠", "\\ne"⟩ -- L_ne
    | `Membership.mem
    | `List.Mem => ⟨51, "∈", "\\in"⟩  -- L_in ∋ \\ni
    | `HasSubset.Subset => ⟨51, "⊆", "\\subseteq"⟩  -- L_subset
    | `Superset => ⟨51, "⊇", "\\supseteq"⟩  -- L_supset
    | `Dvd.dvd => ⟨51, "∣", "\\mid"⟩  -- L_mid
    -- arithmetic operator
    | `HAdd.hAdd => ⟨66, "+", "+"⟩ -- LAdd
    | `HSub.hSub => ⟨66, "-", "-"⟩  -- LSub
    | `HAppend.hAppend => ⟨66, "++", "+\\!\\!+"⟩ -- LAppend
    | `HMul.hMul => ⟨71, "*", "\\cdot"⟩  -- LMul
    | `HDiv.hDiv => ⟨71, "/", "\\frac"⟩  -- LDiv
    | `Rat.divInt => ⟨71, "/", "\\frac"⟩  -- LDiv
    | `HMod.hMod => ⟨71, "%%", "\\%%"⟩  -- LMod
    | `SDiff.sdiff => ⟨71, "\\", "\\setminus"⟩  -- L_setminus
    | `Union.union => ⟨66, "∪", "\\cup"⟩  -- L_cup
    | `Inter.inter => ⟨71, "∩", "\\cap"⟩  -- L_cap
    | `OPlus.oplus => ⟨31, "⊕", "\\oplus"⟩  -- L_oplus
    | `OTimes.otimes => ⟨32, "⊗", "\\otimes"⟩  -- L_otimes
    | `ODot.odot => ⟨73, "⊙", "\\odot"⟩  -- L_odot
    | `Bullet.bullet
    | `HSMul.hSMul => ⟨73, "•", "\\bullet"⟩  -- L_bullet
    | `List.cons => ⟨68, "::", "::"⟩  -- LConstruct
    | `List.Vector.cons => ⟨68, "::ᵥ", "::_v"⟩  -- LVConstruct
    | `Max.max => ⟨68, "⊔", "\\sqcup"⟩  -- L_sqcup
    | `Min.min => ⟨69, "⊓", "\\sqcap"⟩  -- L_sqcap
    | `Dot.dot
    | `List.Vector.dot => ⟨71, "⬝", "{\\color{red}\\cdotp}"⟩  -- L_cdotp
    | `HPow.hPow => ⟨80, "^", "^"⟩  -- LPow
    | `Function.comp => ⟨91, "∘", "\\circ"⟩  -- L_circ
    | _ => panic! s!"BinaryInfix.func : unknown operator {name}"


def BinaryInfix.isProp : BinaryInfix → Bool
  | ⟨name⟩ =>
    match name with
    | `LE.le
    | `GE.ge
    | `LT.lt
    | `GT.gt
    | `Eq
    | `Ne
    | `And
    | `Or
    | `Iff
    | `Membership.mem
    | `List.Mem
    | `HasSubset.Subset
    | `Superset
    | `Dvd.dvd => true
    | _ => false


structure UnaryPrefix where
  name : Name
deriving BEq, CtorName, Repr


def UnaryPrefix.func : UnaryPrefix → Func
  | ⟨name⟩ =>
    match name with
    | `Neg.neg => ⟨68, "-", "-"⟩  -- LNeg
    | `Not => ⟨50, "¬", "\\lnot"⟩  -- L_lnot
    | `Complex.ofReal => ⟨72, "↑", "\\uparrow"⟩  -- L_uparrow
    | `Int.ofNat
    | `Nat.cast
    | `Int.cast
    | `Rat.cast
    | `Subtype.val => ⟨72, "↑", "\\uparrow"⟩  -- L_uparrow
    | `DFunLike.coe => ⟨72, "⇑", "\\Uparrow"⟩  -- LUparrow
    | `Real.sqrt
    | `Root.sqrt => ⟨72, "√", "\\sqrt"⟩  -- L_sqrt
    | `OfNat.ofNat => ⟨107, "cast", ""⟩  -- L_cast
    | _ => panic! s!"UnaryPrefix.func : unknown operator {name}"


def UnaryPrefix.isProp : UnaryPrefix → Bool
  | ⟨`Not⟩ => true
  | _ => false


structure UnaryPostfix where
  name : Name
deriving BEq, Repr


def UnaryPostfix.func: UnaryPostfix → Func
  | ⟨name⟩ =>
    match name with
    | `Inv.inv => ⟨72, "⁻¹", "^{-1}"⟩
    | _ => panic! s!"UnaryPostfix.func : unknown operator {name}"


inductive ExprWithLimits where
  | L_sum
  | L_prod
  | L_int (name : Name)
  | L_bigcap (name : Name)
  | L_bigcup (name : Name)
  | L_lim (name : Name)
  | L_sup (name : Name)
  | L_inf (name : Name)
  | L_max (name : Name)
  | L_min (name : Name)
  | L_forall
  | L_exists
  | L_lambda
  | L_let
deriving BEq, Repr


def ExprWithLimits.func : ExprWithLimits → Func
  | L_sum  => ⟨52, "∑", "\\sum"⟩
  | L_prod => ⟨52, "∏", "\\prod"⟩
  | L_int _ => ⟨52, "∫", "\\int"⟩
  | L_bigcap _ => ⟨52, "⋂", "\\bigcap"⟩
  | L_bigcup _ => ⟨52, "⋃", "\\bigcup"⟩
  | L_lim _ => ⟨52, "lim", "\\lim"⟩
  | L_sup _ => ⟨52, "sup", "\\sup"⟩
  | L_inf _ => ⟨52, "inf", "\\inf"⟩
  | L_max _ => ⟨52, "max", "\\max"⟩
  | L_min _ => ⟨52, "min", "\\min"⟩
  | L_forall => ⟨24, "∀", "\\forall"⟩
  | L_exists => ⟨24, "∃", "\\exists"⟩
  | L_lambda => ⟨72, "fun", "\\operatorname{\\color{magenta}fun}"⟩
  | L_let => ⟨47, "let", "let"⟩


def ExprWithLimits.name : ExprWithLimits → Name
  | L_forall => default
  | L_exists => `Exists
  | L_sum => `Finset.sum
  | L_prod => `Finset.prod
  | L_int name
  | L_bigcap name
  | L_bigcup name
  | L_lim name
  | L_sup name
  | L_inf name
  | L_max name
  | L_min name
  | L_lambda
  | L_let => default


def Binder.func : Binder → Func
  | implicit => ⟨47, "{%s : %s}", "\\left\\lbrace %s : %s\\right\\rbrace"⟩
  | strictImplicit => ⟨47, "⦃%s : %s⦄", "⦃%s : %s⦄"⟩
  | instImplicit => ⟨47, "[%s]", "\\left[%s\\right]"⟩
  | given => ⟨47, "(%s : %s)", "\\left(%s : %s\\right)"⟩
  | default => ⟨47, "(%s : %s)", "\\left(%s : %s\\right)"⟩
  | contains => ⟨47, "%s ∈ %s", "{%s \\in %s}"⟩


structure Special where
  name : Name
deriving BEq, Repr


def Special.func : Special → Func
  | ⟨name⟩ =>
    match name with
    | .anonymous => ⟨72, "__call__", "__call__"⟩
    | `abs => ⟨72, "|%s|", "\\left|%s\\right|"⟩  -- LAbs
    | `Bool.toNat => ⟨72, "Bool.toNat %s", "\\left|%s\\right|"⟩  -- LAbs
    | `Finset.card => ⟨72, "#%s", "\\left|%s\\right|"⟩  -- LCard
    | `Norm.norm => ⟨60, "‖%s‖", "\\left\\lVert%s\\right\\rVert"⟩  -- LNorm
    | `Int.ceil => ⟨72, "⌈%s⌉", "\\left\\lceil%s\\right\\rceil"⟩  -- LCeil
    | `Int.floor => ⟨72, "⌊%s⌋", "\\left\\lfloor%s\\right\\rfloor"⟩  -- LFloor
    | `ite => ⟨60, "ite", "ite"⟩  -- LITE
    | `dite => ⟨60, "ite", "ite"⟩  -- LITE
    | `Subtype.mk
    | `Prod.mk => ⟨117, "⟨%s, %s⟩", "\\langle %s, %s \\rangle"⟩  -- LAngleBracket
    | `List.get
    | `List.Vector.get
    | `GetElem.getElem => ⟨99, "%s[%s]", "%s_%s"⟩  -- LGetElem
    | `GetElem?.getElem? => ⟨99, "%s[%s]?", "%s_{%s?}"⟩  -- LGetElemQue
    | `Nat.ModEq => ⟨32, "%s ≡ %s [MOD %s]", "%s \\equiv %s\\ \\left[\\operatorname{MOD}\\ %s\\right]"⟩  -- L_equiv
    | `Singleton.singleton
    | `Insert.insert => ⟨72, "{%s}", "\\left\\{%s\\right\\}"⟩  -- LBrace
    | `setOf => ⟨72, "{%s | %s}", "\\left\\{%s \\mid %s\\right\\}"⟩  -- LSetOf
    | .str _ "match_1"
    | .str _ "match_2" => ⟨60, "match", "match"⟩  -- L_match
    | `Decidable.decide => ⟨72, "%s", "%s"⟩  -- LDecide
    | _ => panic! s!"Special.func : unknown operator {name}"


inductive ExprWithAttr where
  | L_function (name : Name)
  | L_operatorname (name : Name)
  | LMethod (name : Name)
  | L_typeclass (name : Name)
  | LAttr (name : Name)
deriving BEq, Repr


def ExprWithAttr.func : ExprWithAttr → Func
  | L_function name =>
    let name := name.getLast.toString
    ⟨71, name, "\\" ++ name⟩
  | L_operatorname name =>
    let name := name.getLast.toString
    ⟨
      72,
      name,
      "\\operatorname{%s}".format name.escape_specials
    ⟩
  | LMethod name =>
    let name := name.getLast.toString
    ⟨71, s!"%s.{name} %s", s!"%s.{name.escape_specials}\\ %s"⟩
  | L_typeclass name =>
    let name := name.getLast.toString
    ⟨
      72,
      name,
      "\\operatorname{\\color{#770088}{%s}}".format name.escape_specials
    ⟩
  | LAttr name =>
    let name := name.getLast.toString
    ⟨81, s!".{name}", s!".{name.escape_specials}"⟩


def ExprWithAttr.name : ExprWithAttr → Name
  | L_function name
  | L_operatorname name
  | LMethod name
  | L_typeclass name
  | LAttr name => name


def ExprWithAttr.isProp : ExprWithAttr → Bool
  | .LAttr `IsConstant.is_constant => true
  | _ => false


inductive Operator where
  | BinaryInfix (op : BinaryInfix)
  | UnaryPrefix (op : UnaryPrefix)
  | UnaryPostfix (op : UnaryPostfix)
  | ExprWithLimits (op : ExprWithLimits)
  | Special (op : Special)
  | ExprWithAttr (op : ExprWithAttr)
deriving BEq, CtorName, Repr


def Operator.func : Operator → Func
  | BinaryInfix op => op.func
  | UnaryPrefix op => op.func
  | UnaryPostfix op => op.func
  | ExprWithLimits op => op.func
  | Special op => op.func
  | ExprWithAttr op => op.func


def Operator.priority : Operator → Nat :=
  Func.priority ∘ Operator.func


def Operator.operator : Operator → String :=
  Func.operator ∘ Operator.func


def Operator.name : Operator → Name
  | BinaryInfix op => op.name
  | UnaryPrefix op => op.name
  | UnaryPostfix op => op.name
  | ExprWithLimits op => op.name
  | Special op => op.name
  | ExprWithAttr op => op.name


instance : ToString Operator where
  toString := Operator.operator


def Operator.command : Operator → String :=
  Func.command ∘ Operator.func


inductive Expr where

  | nil

  | const (val : Constant)

  | sort (u : Level)

  | Symbol (name : Name) (type : Expr)

  | Basic (func : Operator) (args : List Expr)

  | Binder (binder : Binder) (binderName : Name) (binderType : Expr) (value : Expr)
deriving Inhabited, BEq, CtorName

def Expr.priority : Expr → Nat
  | nil => 0
  | sort ..
  | Symbol ..
  | const _ => 100
  | Basic op _ => op.priority
  | Binder binder _ _ _ => binder.func.priority


def Expr.isEmpty : Expr → Bool
  | nil => true
  | _ => false


def Expr.isTypeClass : Expr → Bool
  | Basic (.ExprWithLimits .L_forall) (.sort .zero :: _) => true
  | _ => false


def getExprMVarAssignment (mvarId : Lean.MVarId) : MetaM Lean.Expr := do
    if let some e ← Lean.getExprMVarAssignment? mvarId then
      return e
    if let some dAssign ← Lean.getDelayedMVarAssignment? mvarId then
      if let some e' ← Lean.getExprMVarAssignment? dAssign.mvarIdPending then
        let mdecl := (← getMCtx).getDecl dAssign.mvarIdPending
        return ← withLCtx mdecl.lctx mdecl.localInstances do
          let mut e := e'
          let mut binderName := #[]
          let mut binderType := #[]
          for (i, fvar) in dAssign.fvars.mapIdx Prod.mk do
            if let .fvar fvarId := fvar then
              e ← e.subs fvarId i
              let name ←
                if let some decl ← fvarId.findDecl? then
                  pure decl.userName
                else
                  panic! s!"Expr.func.fvar : unknown free variable {fvarId.name}"
              binderName := binderName.push name
              binderType := binderType.push (← inferType fvar)

          return Array.zip binderName binderType |>.foldl (init := e) fun e (name, type) =>
            .lam name type e .implicit
    return .const `«?» []


def «?» := 0


inductive TreeNode where
  | Operator (op : Operator)
  | const (expr : Expr)


partial def Expr.func (e : Lean.Expr) (toExpr : Lean.Expr → List Expr → MetaM Expr) (binders : List Expr) : MetaM TreeNode := do
  match e with
  | .bvar deBruijnIndex  =>
    if h : deBruijnIndex < binders.length then
      return .const binders[deBruijnIndex]
    else
      panic! s!"Expr.func.bvar : unknown deBruijn index {deBruijnIndex} in {binders.length} binders"

  | .fvar fvarId  =>
    if let some decl ← fvarId.findDecl? then
      let type := decl.type
      return .const (Symbol decl.userName (← toExpr type []))
    else
      for (_, mdecl) in (← getMCtx).decls do
        let lctx := mdecl.lctx
        let e : Option TreeNode ← withLCtx lctx mdecl.localInstances do
          if let some decl := lctx.find? fvarId then
            let type := decl.type
            return TreeNode.const (Symbol decl.userName (← toExpr type []))
          else
            return none
        if let some e := e then
          return e
      panic! s!"Expr.func.fvar : unknown free variable {e}"
      -- return .const (Symbol `«?» nil)

  | .mvar mvarId  =>
/-
    if e.toString == "" then
      println! s!"Expr.func.mvar :
e = {e}, e = {← ppExpr e}, e.type = {← inferType e}"
-/
    Expr.func (← getExprMVarAssignment mvarId) toExpr binders

  | .sort u =>
    return .const (sort u)

  | .const declName _  =>
    match declName with
    | `LE.le
    | `LT.lt
    | `GE.ge
    | `GT.gt
    | `Ne
    | `Eq
    | `HAdd.hAdd
    | `HSub.hSub
    | `HAppend.hAppend
    | `HMul.hMul
    | `HPow.hPow
    | `HDiv.hDiv
    | `Rat.divInt
    | `HMod.hMod
    | `And
    | `Or
    | `Iff
    | `Membership.mem
    | `List.Mem
    | `SDiff.sdiff
    | `Inter.inter
    | `Union.union
    | `Function.comp
    | `List.cons
    | `List.Vector.cons
    | `List.Vector.dot
    | `Max.max
    | `Min.min
    | `HasSubset.Subset
    | `Superset
    | `Dvd.dvd
    | `OPlus.oplus
    | `OTimes.otimes
    | `ODot.odot
    | `HSMul.hSMul
    | `Bullet.bullet =>
      return .Operator (.BinaryInfix ⟨declName⟩)

    | `Neg.neg
    | `Not
    | `Real.sqrt
    | `Root.sqrt
    | `Complex.ofReal
    | `Int.ofNat
    | `OfNat.ofNat
    | `Nat.cast
    | `Int.cast
    | `Rat.cast
    | `Subtype.val
    | `DFunLike.coe =>
      return .Operator (.UnaryPrefix ⟨declName⟩)

    | `Inv.inv =>
      return .Operator (.UnaryPostfix ⟨declName⟩)

    | `Real.cos
    | `Real.sin
    | `Real.arccos
    | `Real.arcsin
    | `Complex.arg =>
      return .Operator (.ExprWithAttr (.L_function declName))

    | `List.length
    | `List.tail
    | `List.sum
    | `List.prod
    | `List.flatten
    | `Prod.fst
    | `Prod.snd
    | `List.Vector.length
    | `List.Vector.head
    | `List.Vector.tail
    | `List.Vector.sum
    | `List.Vector.toList
    | `List.Vector.flatten
    | `List.Vector.unflatten
    | `Nat.pred
    | `Nat.succ
    | `Complex.cos
    | `Complex.sin
    | `Complex.exp
    | `Complex.log
    | `IsConstant.is_constant
    | `Tensor.shape
    | `Tensor.args
    | `Int.negSucc =>
      return .Operator (.ExprWithAttr (.LAttr declName))

    | `id
    | `Real.exp
    | `Complex.re
    | `Complex.im
    | `Complex.normSq
    | `Complex.cpow
    | `List.replicate
    | `Finset.range
    | `Set.Ioo
    | `Set.Ico
    | `Set.Iio
    | `Set.Icc
    | `Set.Iic
    | `Set.Ioc
    | `Set.Ici
    | `Set.Ioi
    | `Int.sign
    | `List.Vector.replicate
    | `toIcoDiv
    | `Int.subNatNat =>
      return .Operator (.ExprWithAttr (.L_operatorname declName))

    -- instImplicit
    | `Set
    | `List
    | `Fin
    | `Finset
    | `OPlus
    | `OTimes
    | `ODot
    | `Bullet
    | `List.Vector
    | `Tensor =>
      return .Operator (.ExprWithAttr (.L_typeclass declName))

    | `abs                 -- LAbs
    | `Bool.toNat          -- LAbs
    | `Finset.card         -- LAbs
    | `Norm.norm           -- LNorm
    | `Int.ceil            -- LCeil
    | `Int.floor           -- LFloor
    | `Subtype.mk
    | `Prod.mk             -- LAngleBracket
    | `List.get
    | `List.Vector.get
    | `GetElem.getElem     -- LGetElem
    | `GetElem?.getElem?   -- LGetElemQue
    | `ite                 -- LITE
    | `dite                -- LITE
    | `Singleton.singleton -- LBrace
    | `Insert.insert       -- LBrace
    | `setOf               -- LSetOf
    | `Decidable.decide    -- LDecide
    | `Nat.ModEq =>        -- L_equiv
      return .Operator (.Special ⟨declName⟩)

    | `List.map
    | `List.headD
    | `List.substr
    | `List.Vector.map
    | `List.Vector.headD
    | `List.Vector.substr
    | `Int.fdiv
    | `Int.fmod
    | `Int.tdiv
    | `Int.tmod =>
      return .Operator (.ExprWithAttr (.LMethod declName))

    | `True =>
      return .const (const .True)
    | `False =>
      return .const (const .False)
    | `Infinity =>
      return .const (const .Infinity)
    | `NegativeInfinity =>
      return .const (const .NegativeInfinity)
    | `Infinitesimal =>
      return .const (const .Infinitesimal)
    | `NegativeInfinitesimal =>
      return .const (const .NegativeInfinitesimal)
    | `NaN =>
      return .const (const .NaN)
    | `EmptySet =>
      return .const (const .EmptySet)
    | `UniversalSet =>
      return .const (const .UniversalSet)
    | `Real.pi =>
      return .const (const .Pi)
    | `Complex.I =>
      return .const (const .ImaginaryUnit)
    | `Nat =>
      return .const (const .Nat)
    | `Int =>
      return .const (const .Int)
    | `Rat =>
      return .const (const .Rat)
    | `Real =>
      return .const (const .Real)
    | `List.nil =>
      return .const (const .EmptyList)
    | `Complex =>
      return .const (const .Complex)
    | `Complex.instZero =>
      return .const (const (.natVal 0))
    | `Bool.true =>
      return .const (const .true)
    | `Bool.false =>
      return .const (const .false)

    | `Finset.sum =>
      return .Operator (.ExprWithLimits .L_sum)
    | `Finset.prod =>
      return .Operator (.ExprWithLimits .L_prod)
    | `Exists =>
      return .Operator (.ExprWithLimits .L_exists)

    | .str _ "match_1"
    | .str _ "match_2" =>
      return .Operator (.Special ⟨declName⟩)

    | _ =>
      if Lean.isClass (← Lean.getEnv) declName || (← toExpr (← declName.toConstantInfo).type []).isTypeClass then
        return .Operator (.ExprWithAttr (.L_typeclass declName))
      else
        return .Operator (.ExprWithAttr (.L_operatorname declName))

  | .app fn arg =>
    let op ← Expr.func fn toExpr binders
    match op with
    | .Operator func =>
/-
      if e.toString == "" then
        println! s!"Expr.func.app.Operator :
e = {e}, e = {← ppExpr e}
fn = {fn}, fn = {← ppExpr fn}
arg = {arg}, arg = {← ppExpr arg}
func = {func}
"
-/
      match func with
      | .ExprWithLimits .L_lambda =>
        return .Operator (.Special ⟨default⟩)

      | .UnaryPrefix ⟨`DFunLike.coe⟩ =>
        if arg.ctorName == "const" then
          let arg_func ← Expr.func arg toExpr binders
          match ← Expr.func arg toExpr binders with
          | .Operator (.UnaryPrefix _) =>
            return arg_func
          | _ =>
            return op
        else
          return op
      | _ =>
        return op
    | .const c =>
/-
      if e.toString == "" then
        println! s!"Expr.func.app.const :
e = {e}, e = {← ppExpr e}
fn = {fn}, fn = {← ppExpr fn}, fn.ctoName = {fn.ctorName}
arg = {arg}, arg = {← ppExpr arg}, arg.ctoName = {arg.ctorName}
c.ctorName = {c.ctorName}
"
-/
      match c with
      | Symbol _ (Basic (.ExprWithLimits .L_forall) _) =>
        return .Operator (.Special ⟨default⟩)
      | const .EmptyList =>
        return .const c
      | _ =>
        return .const (.Basic (.Special ⟨default⟩) [c, ← toExpr arg binders])

  | .lam ..  =>
    return .Operator (.ExprWithLimits .L_lambda)

  | .forallE ..  =>
    return .Operator (.ExprWithLimits .L_forall)

  | .letE ..    =>
    return .Operator (.ExprWithLimits .L_let)

  | .lit val =>
    match val with
    | .natVal val =>
      return .const (const (.natVal val))
    | .strVal val =>
      panic! s!"Expr.toExpr :
e = {e}, e.ctorName = {e.ctorName}, val = {val}"

  | .mdata _ e =>
    Expr.func e toExpr binders

  | .proj .. =>
    panic! s!"Expr.toExpr :
e = {e}, e.ctorName = {e.ctorName}"


def Expr.filter_default (func : Operator) (args : List Expr) : MetaM (List Expr × List Expr) := do
  let name := func.name
  match name with
  | .anonymous =>
    return ⟨args, []⟩
  | _ =>
    let binderInfo ← func.name.binderInfo
    return ⟨
      List.zip binderInfo args |>.filterMap fun (binderInfo, arg) =>
        match binderInfo with
        | .default => some arg
        | _ => none,
      args.drop binderInfo.length
    ⟩


def Expr.isProp : Expr → Bool
  | Basic func args =>
    match func, args with
    | .BinaryInfix op, _ => op.isProp
    | .UnaryPrefix op, _ => op.isProp
    | .ExprWithLimits .L_forall, expr :: _ => expr.isProp
    | .ExprWithAttr op, _ => op.isProp
    | .Special ⟨`ite⟩, [_, thenBranch, _] => thenBranch.isProp
    | _, _ => false
  | Symbol _ (sort .zero) => true
  | _ => false


def Binder.mk (binderinfo : BinderInfo) (binderType : Expr) : Binder :=
  match binderinfo with
  | .default => if binderType.isProp then .given else .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit
