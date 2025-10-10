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
    | `Iff => ⟨20, "↔", "\\leftrightarrow"⟩  -- Lean_leftrightarrow, https://github.com/leanprover/lean4/blob/v4.18.0/src/Init/Core.lean#L134
    | `Or => ⟨30, "∨", "\\lor"⟩  -- Lean_lor
    | `or => ⟨30, "||", "||"⟩  -- LeanLogicOr
    | `And => ⟨35, "∧", "\\land"⟩  -- Lean_land
    | `and => ⟨35, "&&", "&&"⟩  -- LeanLogicAnd
    | `LE.le => ⟨50, "≤", "\\le"⟩  -- Lean_le
    | `GE.ge => ⟨50, "≥", "\\ge"⟩  -- Lean_ge
    | `LT.lt => ⟨50, "<", "<"⟩  -- Lean_lt
    | `GT.gt => ⟨50, ">", ">"⟩  -- Lean_gt
    | `Eq => ⟨50, "=", "="⟩  -- LeanEq
    | `Ne => ⟨50, "≠", "\\ne"⟩ -- Lean_ne
    | `BEq.beq => ⟨50, "==", "=="⟩  -- LeanBEq
    | `bne => ⟨50, "!=", "!="⟩  -- Lean_bne
    | `xor => ⟨33, "^^", "^^"⟩  -- Lean_xor
    | `HEq => ⟨50, "≍", "\\asymp"⟩  -- Lean_asymp
    | `SEq => ⟨50, "≃", "\\simeq"⟩  -- Lean_simeq
    | `Membership.mem
    | `List.Mem => ⟨50, "∈", "\\in"⟩  -- Lean_in ∋ \\ni
    | `HasSubset.Subset => ⟨50, "⊆", "\\subseteq"⟩  -- Lean_subseteq
    | `HasSSubset.SSubset => ⟨50, "⊂", "\\subset"⟩  -- Lean_subset
    | `Superset => ⟨50, "⊇", "\\supseteq"⟩  -- Lean_supseteq
    | `SSuperset => ⟨50, "⊃", "\\supset"⟩    -- Lean_supset
    | `Dvd.dvd => ⟨50, "∣", "{\\color{red}{\\ \\mid\\ }}"⟩  -- Lean_mid
    | `HOr.hOr => ⟨55, "|||", "\\mid\\mid\\mid"⟩  -- Lean_HOr
    | `HXor.hXor => ⟨58, "^^^", "\\^\\^\\^"⟩  -- Lean_HXor
    | `HAnd.hAnd => ⟨60, "&&&", "&&&"⟩  -- Lean_HXor
    | `HasEquiv.Equiv => ⟨50, "≈", "≈"⟩
    -- arithmetic operator
    | `Nat.add
    | `HAdd.hAdd => ⟨65, "+", "+"⟩ -- LeanAdd
    | `Nat.sub
    | `HSub.hSub => ⟨65, "-", "-"⟩  -- LeanSub
    | `HAppend.hAppend => ⟨65, "++", "+\\!\\!+"⟩ -- LeanAppend
    | `Mul.mul
    | `HMul.hMul => ⟨70, "*", "\\cdot"⟩  -- LeanMul
    | `Div.div
    | `HDiv.hDiv
    | `Rat.divInt => ⟨70, "/", "\\frac"⟩  -- LeanDiv
    | `HMod.hMod => ⟨70, "%%", "\\%%"⟩  -- LeanMod
    | `HShiftLeft.hShiftLeft => ⟨75, "<<<", "<<<"⟩ -- LeanHShiftLeft
    | `HShiftRight.hShiftRight => ⟨75, ">>>", ">>>"⟩
    | `SDiff.sdiff => ⟨70, "\\", "\\setminus"⟩  -- Lean_setminus
    | `Union.union => ⟨65, "∪", "\\cup"⟩  -- Lean_cup
    | `Inter.inter => ⟨70, "∩", "\\cap"⟩  -- Lean_cap
    | `OPlus.oplus => ⟨30, "⊕", "\\oplus"⟩  -- Lean_oplus
    | `OTimes.otimes => ⟨32, "⊗", "\\otimes"⟩  -- Lean_otimes
    | `ODot.odot => ⟨73, "⊙", "\\odot"⟩  -- Lean_odot
    | `Bullet.bullet
    | `HSMul.hSMul => ⟨73, "•", "\\bullet"⟩  -- Lean_bullet
    | `List.cons => ⟨67, "::", "::"⟩  -- LeanConstruct
    | `List.Vector.cons => ⟨67, "::ᵥ", "::_v"⟩  -- LeanVConstruct
    | `Max.max => ⟨68, "⊔", "\\sqcup"⟩  -- Lean_sqcup
    | `Min.min => ⟨69, "⊓", "\\sqcap"⟩  -- Lean_sqcap
    | `Dot.dot
    | `List.Vector.dot => ⟨70, "⬝", "{\\color{red}\\cdotp}"⟩  -- Lean_cdotp
    | `MatMul.dot => ⟨70, "@", "{\\color{red}\\times}"⟩  -- LeanMatMul
    | `HPow.hPow => ⟨80, "^", "^"⟩  -- LeanPow
    | `Function.comp => ⟨90, "∘", "\\circ"⟩  -- Lean_circ
    | `Prod => ⟨35, "×", "×"⟩  -- Lean_Prod
    | `PProd => ⟨35, "×'", "×'"⟩  -- Lean_Prod
    | `Functor.map => ⟨100, "<$>", "<$>"⟩
    | `Functor.mapRev => ⟨100, "<&>", "<&>"⟩
    | `orM => ⟨30, "<||>", "<||>"⟩
    | `andM => ⟨35, "<&&>", "<&&>"⟩
    | `Bind.bind => ⟨55, ">>=", ">>="⟩
    | `Bind.kleisliRight => ⟨55, ">=>", ">=>"⟩
    | `Bind.kleisliLeft => ⟨55, "<=<", "<=<"⟩
    | `Bind.bindLeft => ⟨55, "=<<", "=<<"⟩
    | `List.IsPrefix => ⟨50, "<+:", "<+:"⟩
    | `List.IsSuffix => ⟨50, "<:+", "<:+"⟩
    | `List.IsInfix => ⟨50, "<:+:", "<:+:"⟩
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
    | `HEq
    | `SEq
    | `And
    | `Or
    | `Iff
    | `Membership.mem
    | `List.Mem
    | `HasSubset.Subset
    | `HasSSubset.SSubset
    | `Superset
    | `SSuperset
    | `Dvd.dvd => true
    | _ => false


structure UnaryPrefix where
  name : Name
deriving BEq, CtorName, Repr


def UnaryPrefix.func : UnaryPrefix → Func
  | ⟨name⟩ =>
    match name with
    | `Neg.neg => ⟨75, "-", "-"⟩  -- LeanNeg
    | `Not => ⟨40, "¬", "\\lnot"⟩  -- Lean_lnot
    | `Bool.not => ⟨40, "!", "\\text{!}"⟩  -- LeanNot
    | `Complement.complement => ⟨100, "~~~", "~~~"⟩
    | `Complex.ofReal
    | `Int.ofNat
    | `Nat.cast
    | `Int.cast
    | `Rat.cast
    | `Fin.val
    | `Finset.toSet
    | `Subtype.val => ⟨72, "↑", "\\uparrow"⟩  -- Lean_uparrow
    | `DFunLike.coe => ⟨72, "⇑", "\\Uparrow"⟩  -- LeanUparrow
    | `Real.sqrt
    | `Root.sqrt => ⟨72, "√", "\\sqrt"⟩  -- Lean_sqrt
    | `OfNat.ofNat => ⟨107, "cast", ""⟩  -- Lean_cast
    | _ => ⟨76, name.toString, name.toString⟩  -- UnaryPrefix resulted from Lean.Expr.proj


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
  | Lean_sum
  | Lean_prod
  | Lean_int (name : Name)
  | Lean_bigcap
  | Lean_bigcup
  | Lean_lim (name : Name)
  | Lean_sup (name : Name)
  | Lean_inf (name : Name)
  | Lean_max (name : Name)
  | Lean_min (name : Name)
  | Lean_forall
  | Lean_exists
  | Lean_lambda
  | Lean_let
deriving BEq, Repr


def ExprWithLimits.func : ExprWithLimits → Func
  | Lean_sum  => ⟨66, "∑", "\\sum"⟩
  | Lean_prod => ⟨71, "∏", "\\prod"⟩
  | Lean_int _ => ⟨52, "∫", "\\int"⟩
  | Lean_bigcap => ⟨52, "⋂", "\\bigcap"⟩
  | Lean_bigcup => ⟨51, "⋃", "\\bigcup"⟩
  | Lean_lim _ => ⟨52, "lim", "\\lim"⟩
  | Lean_sup _ => ⟨52, "sup", "\\sup"⟩
  | Lean_inf _ => ⟨52, "inf", "\\inf"⟩
  | Lean_max _ => ⟨52, "max", "\\max"⟩
  | Lean_min _ => ⟨52, "min", "\\min"⟩
  | Lean_forall => ⟨24, "∀", "\\forall"⟩
  | Lean_exists => ⟨24, "∃", "\\exists"⟩
  | Lean_lambda => ⟨72, "fun", "\\operatorname{\\color{magenta}fun}"⟩
  | Lean_let => ⟨47, "let", "{\\color{blue}{let}}"⟩

def ExprWithLimits.name : ExprWithLimits → Name
  | Lean_forall => default
  | Lean_exists => `Exists
  | Lean_sum => `Finset.sum
  | Lean_prod => `Finset.prod
  | Lean_int name
  | Lean_bigcap => `Set.iInter
  | Lean_bigcup => `Set.iUnion
  | Lean_lim name
  | Lean_sup name
  | Lean_inf name
  | Lean_max name
  | Lean_min name
  | Lean_lambda
  | Lean_let => default


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
    | .anonymous => ⟨75, "__call__", "__call__"⟩
    | `abs => ⟨72, "|%s|", "\\left|%s\\right|"⟩  -- LeanAbs
    | `Bool.toNat => ⟨72, "Bool.toNat %s", "\\left|%s\\right|"⟩  -- LeanAbs
    | `Finset.card => ⟨72, "#%s", "\\left|%s\\right|"⟩  -- LeanCard
    | `Norm.norm => ⟨60, "‖%s‖", "\\left\\lVert%s\\right\\rVert"⟩  -- LeanNorm
    | `Int.ceil => ⟨72, "⌈%s⌉", "\\left\\lceil%s\\right\\rceil"⟩  -- LeanCeil
    | `Int.floor => ⟨72, "⌊%s⌋", "\\left\\lfloor%s\\right\\rfloor"⟩  -- LeanFloor
    | `ite => ⟨60, "ite", "ite"⟩  -- LeanITE
    | `dite => ⟨60, "ite", "ite"⟩  -- LeanITE
    | `List.get
    | `List.Vector.get
    | `Tensor.get
    | `GetElem.getElem => ⟨99, "%s[%s]", "%s_%s"⟩  -- LeanGetElem
    | `GetElem?.getElem? => ⟨99, "%s[%s]?", "%s_{%s?}"⟩  -- LeanGetElemQue
    | `Nat.ModEq => ⟨32, "%s ≡ %s [MOD %s]", "%s \\equiv %s\\ \\left[\\operatorname{MOD}\\ %s\\right]"⟩  -- Lean_equiv
    | `Singleton.singleton
    | `Insert.insert => ⟨72, "{%s}", "\\left\\{%s\\right\\}"⟩  -- LeanBrace
    | `setOf => ⟨72, "{%s | %s}", "\\left\\{%s \\mid %s\\right\\}"⟩  -- LeanSetOf
    | `Decidable.decide => ⟨72, "%s", "%s"⟩  -- LeanDecide
    | .str _ op  =>
      if op.endsWithNumberedWord "match" then
        ⟨60, "match", "match"⟩  -- Lean_match
      else if op == "mk" then
        ⟨117, "⟨%s, %s⟩", "\\langle %s, %s \\rangle"⟩  -- LeanAngleBracket
      else
        panic! s!"Special.func : unknown operator {name}"
    | _ => panic! s!"Special.func : unknown operator {name}"


inductive ExprWithAttr where
  | Lean_function (name : Name)
  | Lean_operatorname (name : Name)
  | Lean_typeclass (name : Name)
  | LeanLemma (name : Name)
  | LeanMethod (name : Name) (idx : Nat) --idx denotes the first index of the self parameter in the default argument list
  | LeanProperty (name : Name)
deriving BEq, Repr


def ExprWithAttr.func : ExprWithAttr → Func
  | Lean_function name =>
    let name := name.getLast.toString
    ⟨75, name, "\\" ++ name⟩
  | Lean_operatorname name =>
    let name := name.getLast.toString
    ⟨
      75,
      name,
      "\\operatorname{%s}".format name.escape_specials
    ⟩
  | Lean_typeclass name =>
    let name := name.getLast.toString
    ⟨
      75,
      name,
      "\\operatorname{\\color{#770088}{%s}}".format name.escape_specials
    ⟩
  | LeanLemma name =>
    let name := name.getLast.toString
    ⟨75, "⋯", "\\cdots"⟩
  | LeanMethod name idx =>
    let name := name.getLast.toString
    ⟨75, s!"%s.{name} %s", s!"%s.{name.escape_specials}\\ %s"⟩
  | LeanProperty name =>
    let name := name.getLast.toString
    ⟨81, s!".{name}", s!".{name.escape_specials}"⟩


def ExprWithAttr.name : ExprWithAttr → Name
  | Lean_function name
  | Lean_operatorname name
  | Lean_typeclass name
  | LeanLemma name
  | LeanMethod name idx
  | LeanProperty name => name


def ExprWithAttr.isProp : ExprWithAttr → Bool
  | .LeanProperty `IsConstant.is_constant => true
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

def Operator.methodIdx : Operator → Nat
  | ExprWithAttr (.LeanMethod _ idx) => idx
  | _ => 0


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
  | Basic (.ExprWithLimits .Lean_forall) (.sort .zero :: _) => true
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


def ExprWithAttr.toTreeNode (declName : Name) (toExpr : Lean.Expr → List Expr → MetaM Expr) : MetaM TreeNode := do
  let op : Name → ExprWithAttr ←
    if Lean.isClass (← Lean.getEnv) declName then
      pure ExprWithAttr.Lean_typeclass
    else
      if (← toExpr (← declName.toConstantInfo).type []).isTypeClass then
        pure ExprWithAttr.Lean_typeclass
      else
        match declName with
        | .anonymous
        | .num _ _
        | .str .anonymous _ =>
          pure ExprWithAttr.Lean_operatorname
        | .str classname _ =>
          let binderInfo ← declName.binderInfo
          let binderType ← declName.binderType
          let defaultType :=
            List.zip binderInfo binderType |>.filterMap fun (binderInfo, binderType) =>
            match binderInfo with
              | .default => some binderType.declName
              | _ => none
          if let some idx := defaultType.idxOf? classname then
            if defaultType.length == 1 then
              pure ExprWithAttr.LeanProperty
            else if ← declName.is_Lemma then
              pure ExprWithAttr.LeanLemma
            else
              pure (fun name : Name => ExprWithAttr.LeanMethod name idx)
          else if ← declName.is_Lemma then
            pure ExprWithAttr.LeanLemma
          else
            pure ExprWithAttr.Lean_operatorname
  return .Operator (.ExprWithAttr (op declName))

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
      Lean.logInfo s!"Expr.func.mvar :
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
    | `Eq
    | `Ne
    | `HEq
    | `SEq
    | `Nat.add
    | `HAdd.hAdd
    | `Nat.sub
    | `HSub.hSub
    | `HAppend.hAppend
    | `Mul.mul
    | `HMul.hMul
    | `HPow.hPow
    | `Div.div
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
    | `MatMul.dot
    | `Max.max
    | `Min.min
    | `HasSubset.Subset
    | `HasSSubset.SSubset
    | `Superset
    | `SSuperset
    | `Dvd.dvd
    | `OPlus.oplus
    | `OTimes.otimes
    | `ODot.odot
    | `HSMul.hSMul
    | `Bullet.bullet =>
      return .Operator (.BinaryInfix ⟨declName⟩)

    | `Neg.neg
    | `Not
    | `Bool.not
    | `Real.sqrt
    | `Root.sqrt
    | `Complex.ofReal
    | `Int.ofNat
    | `OfNat.ofNat
    | `Nat.cast
    | `Int.cast
    | `Rat.cast
    | `Fin.val
    | `Finset.toSet
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
      return .Operator (.ExprWithAttr (.Lean_function declName))

    | `id
    | `Exp.exp
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
    | `Finset.Ioo
    | `Finset.Ico
    | `Finset.Iio
    | `Finset.Icc
    | `Finset.Iic
    | `Finset.Ioc
    | `Finset.Ici
    | `Finset.Ioi
    | `Int.sign
    | `List.Vector.replicate
    | `toIcoDiv
    | `Int.subNatNat =>
      return .Operator (.ExprWithAttr (.Lean_operatorname declName))

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
      return .Operator (.ExprWithAttr (.Lean_typeclass declName))

    | `abs                 -- LeanAbs
    | `Bool.toNat          -- LeanAbs
    | `Finset.card         -- LeanAbs
    | `Norm.norm           -- LeanNorm
    | `Int.ceil            -- LeanCeil
    | `Int.floor           -- LeanFloor
    | `List.get
    | `List.Vector.get
    | `Tensor.get
    | `GetElem.getElem     -- LeanGetElem
    | `GetElem?.getElem?   -- LeanGetElemQue
    | `ite                 -- LeanITE
    | `dite                -- LeanITE
    | `Singleton.singleton -- LeanBrace
    | `Insert.insert       -- LeanBrace
    | `setOf               -- LeanSetOf
    | `Decidable.decide    -- LeanDecide
    | `Nat.ModEq =>        -- Lean_equiv
      return .Operator (.Special ⟨declName⟩)

    | `True =>
      return .const (const .True)
    | `False =>
      return .const (const .False)
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
      return .const (const (.ident declName))
    | `Complex =>
      return .const (const .Complex)
    | `Complex.instZero =>
      return .const (const (.natVal 0))
    | `Bool.true =>
      return .const (const .true)
    | `Bool.false =>
      return .const (const .false)

    | `Finset.sum =>
      return .Operator (.ExprWithLimits .Lean_sum)
    | `Finset.prod =>
      return .Operator (.ExprWithLimits .Lean_prod)
    | `Exists =>
      return .Operator (.ExprWithLimits .Lean_exists)
    | `Set.iUnion =>
      return .Operator (.ExprWithLimits .Lean_bigcup)
    | `Set.iInter =>
      return .Operator (.ExprWithLimits .Lean_bigcap)

    | .str _ op =>
      if op.endsWithNumberedWord "match" || op == "mk" then
        return .Operator (.Special ⟨declName⟩)
      else
        ExprWithAttr.toTreeNode declName toExpr
    | _ =>
      ExprWithAttr.toTreeNode declName toExpr

  | .app fn arg =>
    let op ← Expr.func fn toExpr binders
    match op with
    | .Operator func =>
/-
      if e.toString == "" then
        Lean.logInfo s!"Expr.func.app.Operator :
e = {e}, e = {← ppExpr e}
fn = {fn}, fn = {← ppExpr fn}
arg = {arg}, arg = {← ppExpr arg}
func = {func}
"
-/
      match func with
      | .ExprWithLimits .Lean_lambda =>
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
        Lean.logInfo s!"Expr.func.app.const :
e = {e}, e = {← ppExpr e}
fn = {fn}, fn = {← ppExpr fn}, fn.ctoName = {fn.ctorName}
arg = {arg}, arg = {← ppExpr arg}, arg.ctoName = {arg.ctorName}
c.ctorName = {c.ctorName}
"
-/
      match c with
      | Symbol _ (Basic (.ExprWithLimits .Lean_forall) _) =>
        return .Operator (.Special ⟨default⟩)
      | const (.ident `List.nil) =>
        return .const c
      | _ =>
        return .const (.Basic (.Special ⟨default⟩) [c, ← toExpr arg binders])

  | .lam ..  =>
    return .Operator (.ExprWithLimits .Lean_lambda)

  | .forallE ..  =>
    return .Operator (.ExprWithLimits .Lean_forall)

  | .letE ..    =>
    return .Operator (.ExprWithLimits .Lean_let)

  | .lit val =>
    match val with
    | .natVal val =>
      return .const (const (.natVal val))
    | .strVal val =>
      return .const default

  | .mdata _ e =>
    Expr.func e toExpr binders

  | .proj typeName idx _ =>
    return .Operator (.UnaryPrefix ⟨← typeName.projFieldName idx⟩)

def Expr.filter_default (func : Operator) (args : List Expr) : MetaM (List Expr × List Expr) := do
  let name := func.name
  if name == default then
    return ⟨args, []⟩
  else
    let binderInfo ← name.binderInfo
    return ⟨
      List.zip binderInfo args |>.filterMap fun (binderInfo, arg) =>
        if binderInfo == .default then
          some arg
        else
          none,
      args.drop binderInfo.length
    ⟩


def Expr.isProp : Expr → Bool
  | Basic func args =>
    match func, args with
    | .BinaryInfix op, _ => op.isProp
    | .UnaryPrefix op, _ => op.isProp
    | .ExprWithLimits .Lean_forall, expr :: _ => expr.isProp
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
