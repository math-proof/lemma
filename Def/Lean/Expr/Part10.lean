import Def.Lean.Meta.Expr.Part4
import Notation.Lean.Expr.Singleton
import Inductive.Lean.Expr.Part5
open Lean.Meta
open Lean (Name Json Level BinderInfo getMCtx)
set_option linter.unusedVariables false


def ExprWithAttr.toTreeNode (declName : Name) (toExpr : Lean.Expr → List Expr → Nat → MetaM Expr) (level : Nat) : MetaM TreeNode := do
  let op : Name → ExprWithAttr ←
    if Lean.isClass (← Lean.getEnv) declName then
      pure ExprWithAttr.Lean_typeclass
    else
      if (← toExpr (← declName.toConstantInfo).type [] level).isTypeClass then
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

partial def Expr.func (e : Lean.Expr) (toExpr : Lean.Expr → List Expr → Nat → MetaM Expr) (binders : List Expr) (level : Nat) : MetaM TreeNode := do
  match e with
  | .bvar deBruijnIndex  =>
    if h : deBruijnIndex < binders.length then
      return .const binders[deBruijnIndex]
    else
      panic! s!"Expr.func.bvar : unknown deBruijn index {deBruijnIndex} in {binders.length} binders"

  | .fvar fvarId  =>
    if let some decl ← fvarId.findDecl? then
      let type := decl.type
      return .const (Symbol decl.userName (← toExpr type [] level))
    else
      for (_, mdecl) in (← getMCtx).decls do
        let lctx := mdecl.lctx
        let e : Option TreeNode ← withLCtx lctx mdecl.localInstances do
          if let some decl := lctx.find? fvarId then
            let type := decl.type
            return TreeNode.const (Symbol decl.userName (← toExpr type [] level))
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

    Expr.func (← getExprMVarAssignment mvarId) toExpr binders level

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
    | `HasEquiv.Equiv
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
    | `HShiftLeft.hShiftLeft
    | `HShiftRight.hShiftRight
    | `HOr.hOr
    | `HXor.hXor
    | `HAnd.hAnd
    | `And
    | `Or
    | `Iff
    | `Membership.mem
    | `List.Mem
    | `SDiff.sdiff
    | `Inter.inter
    | `Union.union
    | `Function.comp
    | `Dot.dot
    | `List.cons
    | `List.Vector.cons
    | `List.Vector.dot
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
    | `Bullet.bullet
    | `Matrix.mulVec
    | `dotProduct =>
      return .Operator (.BinaryInfix ⟨declName⟩)

    | `Neg.neg
    | `Not
    | `Bool.not
    | `Real.sqrt
    | `Root.sqrt
    | `Root.cubic
    | `Root.quartic
    | `Complex.conj
    | `Star.star
    | `Complex.ofReal
    | `Hyperreal.ofReal
    | `Int.ofNat
    | `OfNat.ofNat
    | `Nat.cast
    | `Int.cast
    | `Rat.cast
    | `Fin.val
    | `Finset.toSet
    | `Subtype.val =>
      return .Operator (.UnaryPrefix ⟨declName⟩)

    | `DFunLike.coe =>
      -- `coe` has two explicit args (F, a) despite being unary notation `⇑ F` in source
      return .Operator (.ExprWithAttr (.Lean_operatorname declName))

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
    | `tsum =>
      return .Operator (.ExprWithLimits .Lean_tsum)
    | `Finset.prod =>
      return .Operator (.ExprWithLimits .Lean_prod)
    | `Filter.limUnder =>
      return .Operator (.ExprWithLimits .Lean_lim)
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
        ExprWithAttr.toTreeNode declName toExpr level
    | _ =>
      ExprWithAttr.toTreeNode declName toExpr level

  | .app fn arg =>
    let op ← Expr.func fn toExpr binders level
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
          let arg_func ← Expr.func arg toExpr binders level
          match ← Expr.func arg toExpr binders level with
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
      | Symbol _ (Basic (.ExprWithLimits .Lean_forall) ..) =>
        return .Operator (.Special ⟨default⟩)
      | const (.ident `List.nil) =>
        return .const c
      | _ =>
        return .const (.Basic (.Special ⟨default⟩) [c, ← toExpr arg binders level] level)

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
    Expr.func e toExpr binders level

  | .proj typeName idx _ =>
    return .Operator (.UnaryPrefix ⟨← typeName.projFieldName idx⟩)

def Expr.filter_default (func : Operator) (args : List Expr) : MetaM (List Expr × List Expr) := do
  let name := func.name
  if name == default then
    return ⟨args, []⟩
  else
    let binderInfo ← name.binderInfo
    let filtered := List.zip binderInfo args |>.filterMap fun (binderInfo, arg) =>
      if binderInfo == .default then some arg else none
    let extra := args.drop binderInfo.length
    return ⟨filtered, extra⟩


def Expr.isProp : Expr → Bool
  | Basic func args _ =>
    match func, args with
    | .BinaryInfix op, _ => op.isProp
    | .UnaryPrefix op, _ => op.isProp
    | .ExprWithLimits .Lean_forall, expr :: _ => expr.isProp
    | .ExprWithAttr op, _ => op.isProp
    | .Special ⟨`ite⟩, [_, thenBranch, _] => thenBranch.isProp
    | _, _ => false
  | Symbol _ (sort .zero) => true
  | _ => false

/-- True when `e` is marked as a random variable type via `RandomVariable` wrapper
(see `parser.lean` where `MeasurableSpace` instances are synthesized). -/
def Expr.isRandomVariable : Expr → Bool
  | Basic (.ExprWithAttr (.Lean_operatorname `RandomVariable)) [_] _ => true
  | _ => false


def Binder.mk (binderinfo : BinderInfo) (binderType : Expr) : Binder :=
  match binderinfo with
  | .default => if binderType.isProp then .given else .default
  | .implicit => .implicit
  | .strictImplicit => .strictImplicit
  | .instImplicit => .instImplicit


def Expr.isNatZero : Expr → Bool
  | const (.natVal 0) => true
  | _ => false

