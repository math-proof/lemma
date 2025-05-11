import sympy.core.expr
import sympy.printing.str
import stdlib.Lean.BinderInfo
import stdlib.Lean.Expr
open Lean.Meta
open Lean (Name Level Literal FormatWithInfos PPContext getExprMVarAssignment? getEnv getConstInfo getLCtx BinderInfo)
set_option linter.unusedVariables false


def Expr.replace (e : Expr) (name : Name) (name' : Name) (type : Expr) : Expr :=
  match e with
  | Symbol name'' type' =>
    if name'' == name && type == type' then
      Symbol name' type
    else
      e
  | Basic func args =>
    Expr.Basic func (map args)
  | Binder binder binderName binderType value =>
    if binderName == name && binderType == type then
      Expr.Binder binder name' type value
    else
      Expr.Binder binder binderName (binderType.replace name name' type) value
  | _ =>
    e
where
  map : List Expr → List Expr
  | [] => []
  | head :: tail => head.replace name name' type :: map tail


def Expr.merge (func : Operator) (expr : List Expr) (limits : List Expr) : Expr :=
  let list : Option (List Expr) :=
    match expr.getLast?, limits with
    | some (Binder binderInfo binderName binderType value), [Binder binderInfo' binderName' binderType' value'] =>
      if binderInfo == binderInfo' && binderType == binderType' && value == value' then
        expr.dropLast ++ [Binder binderInfo (binderName' ++ binderName) binderType value]
      else
        none
    | _, _ =>
      none
  match list with
  | some expr =>
    Basic func expr
  | none =>
    Basic func (expr ++ limits)


def Expr.joinWithAnd : List Expr → Expr
  | .nil =>
    .nil
  | [head] =>
    head
  | head :: tail =>
    .Basic (.BinaryInfix ⟨`And⟩) [head, Expr.joinWithAnd tail]


partial def Expr.toExpr (e : Lean.Expr) (binders : List Expr) : MetaM Expr := do
  match ← Expr.func e Expr.toExpr binders with
  | .Operator func =>
    let res ← match_condition_set e binders
    if res != nil then
      return res

    let full_args ← get_args e binders func
    let ⟨args, extra_args⟩ ← Expr.filter_default func full_args
/-
    if e.toString == "" then
      println! s!"Expr.toExpr.Operator :
e = {e}
e = {← ppExpr e}, e.ctorName = {e.ctorName}
func = {func}, func.ctorName = {func.ctorName}
binders = {binders}
full_args.length = {full_args.length} :
{"\n".intercalate (full_args.map fun arg => arg.toString)}
args.length = {args.length} :
{"\n".intercalate (args.map fun arg => arg.toString)}
"
-/
    let expr ← construct_from_args e binders func args
    if extra_args == .nil then
      return expr
    return Basic (.Special ⟨default⟩) (expr :: extra_args)
  | .const expr =>
/-
    if e.toString == "" then
      println! s!"Expr.toExpr.const :
e = {e}, e = {← ppExpr e}, e.ctorName = {e.ctorName}
expr = {expr}, expr.ctorName = {expr.ctorName}
"
-/
    return expr
where
  get_args (e : Lean.Expr) (binders : List Expr) (func : Operator) : MetaM (List Expr) := do
    match e with
    | .bvar deBruijnIndex  =>
      match func, binders[deBruijnIndex]? with
      | .Special ⟨.anonymous⟩, some e@(Symbol _ (Basic (.ExprWithLimits .L_forall) _)) =>
        return [e]
      | _, _ =>
        return []

    | .fvar fvarId =>
      match func with
      | .Special ⟨.anonymous⟩ =>
        match ← fvarId.findDecl? with
        | some decl =>
          return [Symbol decl.userName (← Expr.toExpr decl.type [])]
        | none =>
          panic! s!"fvarId.findDecl? failed for {fvarId}"
      | _ =>
        return []

    | .mvar mvarId  =>
      get_args (← getExprMVarAssignment mvarId) binders func

    | .const ..  =>
      return []

    | .app e_fn e_arg =>
      let args ← get_args e_fn binders func
      let arg ← Expr.toExpr e_arg binders
/-
      if e.toString == "" then
        println! s!"Expr.toExpr.get_args.app :
func = {func}
e = {e}
e = {← ppExpr e}
e_fn = {e_fn}
e_fn = {← ppExpr e_fn}
e_fn.args :
{"\n".intercalate (args.map fun arg => arg.toString)}
e_arg = {e_arg}
e_arg = {← ppExpr e_arg}
e_arg = {arg}
binders = {binders}
"
-/
      return args ++ [arg]

    | .lam binderName binderType body binderInfo
    | .forallE binderName binderType body binderInfo =>
      args_from_binders binderName binderType body binderInfo nil

    | .letE binderName binderType value body _    =>
      -- binderName : binderType := value; body
      args_from_binders binderName binderType body BinderInfo.default (← Expr.toExpr value binders)

    | .mdata _ e =>
      get_args e binders func

    | _     =>
      return []

  args_from_binders (binderName : Name) (binderType : Lean.Expr) (body : Lean.Expr) (binderInfo : BinderInfo) (value : Expr) : MetaM (List Expr) := do
    let binderType ← Expr.toExpr binderType binders
    let binderName ←
      if ← body.contains binderName then
        pure (Name.anonymous.str (binderName.toString ++ "'"))
      else
        pure binderName
    let binders := Expr.Symbol binderName binderType :: binders
    let body' ← Expr.toExpr body binders
    let binderName := binderName.head
    let binderInfo := Binder.mk binderInfo binderType
/-
      if e.toString == "" then
        println! s!"Expr.toExpr.args_from_binders :
e = {e}
e = {← ppExpr e}
binders = {binders}
binderName = {binderName}
binderType = {binderType}
binderInfo = {binderInfo}
body = {body}
body' = {body'}
"
-/

    return [body', Expr.Binder binderInfo binderName binderType value]

  match_condition_set (e : Lean.Expr) (binders : List Expr) : MetaM Expr := do
    if let .app (.app (.const `setOf _) type) (.lam var type' cond .default) := e then
      if type' == type then
/-
        println! s!"Expr.toExpr.setOf.app :
type = {type}
cond = {cond}
cond = {← ppExpr cond}
"
-/
        if let .app
            (.app
              (.app
                (.const (.str _ match_d) _)
                (.lam var' type' (.sort .zero) .default)
              )
              (.bvar .zero)
            )
            (.lam arg0 type0 (.lam arg1 type1 cond .default) .default) := cond then
/-
        println! s!"Expr.toExpr.setOf.app :
var' = {var'}
var = {var}
type' = {type'}
type = {type}
cond = {cond}
cond = {← ppExpr cond}
"
-/
          -- var', var might not be the same
          match match_d with
          | "match_1"
          | "match_2" =>
            if type' == type then -- && var' == var
              if let (.app (.app (.const `Prod _) type0') type1') := type then
                if type0' == type0 && type1' == type1 then
                  let type0 ← Expr.toExpr type0 binders
                  let type ← Expr.toExpr type binders
                  let type1 ← Expr.toExpr type1 binders
                  let symbols := [Symbol arg0 type0, Symbol arg1 type1]
                  let expr := Basic (.Special ⟨`Prod.mk⟩) symbols
                  let cond ← Expr.toExpr cond ((Symbol var type :: symbols).reverse ++ binders)
                  return Basic (.Special ⟨`setOf⟩) [expr, cond]
          | _ =>
            pure ()
        else
          let type ← Expr.toExpr type binders
          let expr := Symbol var type
          let cond ← Expr.toExpr cond (expr :: binders)
          return Basic (.Special ⟨`setOf⟩) [expr, cond]
    return nil

  construct_from_args (e : Lean.Expr) (binders : List Expr) (func : Operator) (args : List Expr) : MetaM Expr := do
    match func with
    | .UnaryPrefix ⟨name⟩ =>
      match name with
      | `OfNat.ofNat =>
        if let [arg] := args then
          return arg
      | `DFunLike.coe =>
        if let const (.ident name) :: args@(.cons ..) := args then
          return Basic (.ExprWithAttr (.L_operatorname name)) args
      | _ =>
        pure ()
    | .ExprWithLimits op =>
      if let arg :: limits := args then
        match arg with
        | Basic (.ExprWithLimits op') expr =>
          if op == op' then
            let simplify :=
              match op, limits with
              | .L_forall, [Binder .implicit _ (.sort (.succ _)) nil] =>
                -- ignore {α : Type u_1}
                true
              | .L_forall, [Binder .default var binderType@(Symbol _ type@(sort (.succ _))) nil] =>
                -- simplify membership : ∀ (x : α) (a : x ∈ X), x = x0 => ∀ x ∈ X, x = x0
                match expr with -- expr = [x = x0, (a : x ∈ X)]
                | [_, Binder .given _ (Basic (.BinaryInfix ⟨`Membership.mem⟩) [_, Symbol var' binderType']) nil] =>
                  var == var' && binderType == binderType'
                | _ =>
                  false
              | _, _ =>
                false
            return if simplify then arg else Expr.merge func expr limits
          else if op == .L_exists && op' == .L_lambda && limits == [] then
            if let [expr, limit@(Binder .default _ _ nil)] := expr then
              return Basic func [expr, limit]
        | scope =>
          match op with
          | .L_sum
          | .L_prod =>
            if let [Basic (.ExprWithLimits .L_lambda) [expr, Binder .default name type nil]] := limits then
              return Basic func [expr, Binder .contains name scope nil]
          | _ =>
            pure ()
    | .Special ⟨op⟩ =>
      match op with
      | .anonymous =>
        -- simplify function call if the argument is the same as the binder name of the lambda function
        match args with
        | [expr, Binder .implicit name type nil, Symbol name' type']
        | [Basic (.ExprWithLimits .L_lambda) [expr, Binder .implicit name type nil], Symbol name' type'] =>
          if type == type' then
            if name == name' then
              return expr
            else
              return expr.replace name name' type
        | [expr, limit@(Binder .default ..), arg] =>
          return Basic func [Basic (.ExprWithLimits .L_lambda) [expr, limit], arg]
        | _ =>
          pure ()
      | .str _ "match_1"
      | .str _ "match_2" =>
        -- transform match expression into if-then-else structure
        let args' := args.drop 1
        if let some index := args'.findIdx? fun arg =>
          match arg with
          | Basic (.ExprWithLimits .L_lambda) _ => true
          | _ => false then
          let subject := args'.take index
          let values := args'.drop index
          if let .forallE name type body _  ← op.toExpr then
            let binders := Expr.Symbol name (← Expr.toExpr type binders) :: binders
            let ⟨body, binders⟩ : Lean.Expr × List Expr :=
              if let (.forallE name type body .default) := body then
                ⟨body, Expr.Symbol name (← Expr.toExpr type binders) :: binders⟩
              else
                ⟨body, binders⟩
            return ← construct_ite e body binders subject values
      | `dite =>
        if let [_, Basic (.ExprWithLimits .L_lambda) [thenBranch, ifBranch], Basic (.ExprWithLimits .L_lambda) (elseBranch :: _)] := args then
          return Basic (.Special ⟨`ite⟩) [ifBranch, thenBranch, elseBranch]
      | _ =>
        pure ()
    | .ExprWithAttr (.L_operatorname name) =>
      if args == [] then
        return const (Constant.ident name)
    | .BinaryInfix ⟨`HDiv.hDiv⟩ =>
      if e.isIntDiv then
        return Basic (.ExprWithAttr (.LMethod `Int.ediv 0)) args
    | _ =>
      pure ()
    return Basic func args

  construct_ite (e body : Lean.Expr) (binders subject values : List Expr) : MetaM Expr := do
    let mut body := body
    let mut cases : Array (Expr × Expr) := #[]
    let mut localBinders := binders
    for expr in values do
      if let Basic (.ExprWithLimits .L_lambda) (expr :: expr_tail) := expr then
        if let .forallE name binderType body' _ := body then
          localBinders := Expr.Symbol name (← Expr.toExpr binderType localBinders) :: localBinders
          body := body'
          match binderType with
          | .forallE .anonymous (.const `Unit _) (.app _ caseValue) .default =>
            cases := cases.push ⟨
              Basic (.BinaryInfix ⟨`Eq⟩) [subject.head!, ← Expr.toExpr caseValue binders],
              expr
            ⟩
          | .const declName _ =>
            if let .forallE _ binderType body' .default := body then
              body := body'
              let caseValue := binderType.extract_conditions subject.length
              if let .forallE var type binderType .default := binderType then
                localBinders := Expr.Symbol var (← Expr.toExpr type localBinders) :: localBinders
                cases := cases.push ⟨
                  Expr.joinWithAnd (List.zipWith
                    (fun key val => Basic (.BinaryInfix ⟨`Eq⟩) [key, val])
                    subject
                    (← caseValue.mapM fun cond => Expr.toExpr cond localBinders)
                  ),
                  expr
                ⟩
          | .forallE var type binderType .default =>
            let mut binderType := binderType
            let type ← Expr.toExpr type localBinders
            localBinders := Expr.Symbol var type :: localBinders
            let mut caseValue := .nil
            if let .forallE var type binderType' .default := binderType then
              let type ← Expr.toExpr type localBinders
              localBinders := Expr.Symbol var type :: localBinders
              binderType := binderType'
            caseValue := binderType.extract_conditions_recursively subject.length []
            cases := cases.push ⟨
              Expr.joinWithAnd (List.zipWith
                (fun key val => Basic (.BinaryInfix ⟨`Eq⟩) [key, val])
                subject
                (← caseValue.mapM fun cond => Expr.toExpr cond localBinders)
              ),
              expr
            ⟩
          | _ =>
            break
    let mut ite : Expr := nil
    for ⟨cond, expr⟩ in cases.reverse do
      if ite == nil then
        ite := expr
      else
        ite := Basic (.Special ⟨`ite⟩) [cond, expr, ite]

    return ite
