module

public import Mathlib.Analysis.Calculus.Gradient.Basic

public meta section

syntax:max (name := gradSugar) "∇[" ident "] " term:67 : term

/-- `∇[θ = θ₀] expr`: the gradient of `expr` with respect to `θ`, evaluated at `θ₀`. -/
syntax:max (name := gradAtSugar) "∇[" ident " = " term "] " term:67 : term

open Lean Elab Term Meta in
/-- Strip outer term parentheses so `∇[θ] (F θ)` and `∇[θ] F θ` share one match. -/
private partial def stripParens : Term → Term
  | `(($e)) => stripParens e
  | e => e

open Lean Elab Term Meta in
/-- `true` when `fun x ↦ body` returns a function, i.e. its codomain `ι → 𝕜` (after
`whnf`, e.g. `Fin n → ℝ`) is itself a `forallE`. Such a body is vector-valued, so `∇`
takes the componentwise gradient. A scalar codomain `𝕜` (or anything else) stays on
Mathlib's `gradient`. The probe term is discarded; the caller elaborates the body again. -/
private def isVectorBody (x : Ident) (body : Term) : TermElabM Bool := do
  let saved ← saveState
  let vec ← try
      let lam ← withoutErrToSorry <| elabTerm (← `(fun $x:ident ↦ $body)) none
      let ty ← whnf (← inferType lam)
      match ty with
      | .forallE _ _ cod _ => pure (← whnf cod).isForall
      | _ => pure false
    catch ex =>
      if let .internal id _ := ex then
        if id == postponeExceptionId then throw ex
      pure false
  saved.restore
  return vec

open Lean Elab Term Meta in
/-- Scalar expansion unless `body` is vector-valued, then the componentwise gradient
`fun j ↦ gradient (fun x ↦ body j) p`. Elaborate the vector expansion independently of
the expected type so a matrix-shaped expectation cannot specialize the gradient's domain. -/
private def elabGradBody (x : Ident) (b body p : Term) (expectedType? : Option Expr) :
    TermElabM Expr := do
  if ← isVectorBody x b then
    let e ← elabTerm (← `(fun j => gradient (fun $x:ident ↦ $b j) $p)) none
    ensureHasType expectedType? e
  else
    let stx ← `(gradient (fun $x:ident ↦ $body) $p)
    let saved ← saveState
    try
      withoutErrToSorry <| elabTerm stx expectedType?
    catch ex =>
      if let .internal id _ := ex then
        if id == postponeExceptionId then throw ex
      -- A function-shaped expected type can specialize the gradient's domain instead of
      -- its result. Retry independently only when ordinary scalar elaboration fails.
      saved.restore
      let e ← elabTerm stx none
      ensureHasType expectedType? e

open Lean Elab Term Meta in
/-- `∇[x] body` at `p = x`, or `∇[x = p] body` at the given `p`.

Scalar bodies keep the syntactic expansions (definitionally unchanged):
scalar `∇[x] f x` (with `x` the last explicit argument) ↦ `gradient f p`, and
`∇[x] j` ↦ `gradient j p`. The bare identifier stays scalar; every other body is
checked for a function codomain and, when vector-valued, expands to the componentwise
gradient `fun j ↦ gradient (fun x ↦ body j) p`. Other scalar bodies use the lambda form
`gradient (fun x ↦ body) p`. -/
private def elabGrad (x : Ident) (body p : Term) (expectedType? : Option Expr) :
    TermElabM Expr := do
  let b := stripParens body
  match b with
  | `($f $y:ident) =>
    if y.getId == x.getId && !(← isVectorBody x b) then
      elabTerm (← `(gradient $f $p)) expectedType?
    else
      elabGradBody x b body p expectedType?
  | `($j:ident) =>
    elabTerm (← `(gradient $j $p)) expectedType?
  | _ =>
    elabGradBody x b body p expectedType?

open Lean Elab Term Meta in
@[term_elab gradSugar]
def elabGradSugar : TermElab := fun stx expectedType? => do
  let `(∇[$x:ident] $body) := stx | throwUnsupportedSyntax
  elabGrad x body ⟨x.raw⟩ expectedType?

open Lean Elab Term Meta in
@[term_elab gradAtSugar]
def elabGradAtSugar : TermElab := fun stx expectedType? => do
  let `(∇[$x:ident = $p] $body) := stx | throwUnsupportedSyntax
  elabGrad x body p expectedType?

open Lean PrettyPrinter Delaborator SubExpr in
/-- Infoview: `gradient (fun x ↦ body) p` as `∇[x] body` (or `∇[x = p] body` when the
evaluation point is not the bound variable); `gradient f p` as `∇[x] f x`. -/
@[app_delab gradient]
meta def delabGradient : Delab := whenNotPPOption getPPExplicit do
  let e := (← getExpr).consumeMData
  let args := e.getAppArgs
  guard <| args.size >= 2
  let f := args[args.size - 2]!
  let p := args[args.size - 1]!
  if f.isLambda then
    let x := f.bindingName!
    let bound ← if p.isFVar then
      match (← getLCtx).find? p.fvarId! with
      | some d => pure (d.userName.eraseMacroScopes == x.eraseMacroScopes)
      | none => pure true
    else pure false
    descend f 0 do
      withBindingBodyUnusedName fun n => do
        let body ← delab
        let xid : TSyntax `ident := ⟨n⟩
        if bound then
          `(∇[$xid] $body)
        else
          descend p 1 do
            let p' ← delab
            `(∇[$xid = $p'] $body)
  else
    let xid : TSyntax `ident := if p.isFVar then mkIdent p.fvarId!.name else mkIdent `x
    descend f 0 do
      let fn ← delab
      descend p 1 do
        `(∇[$xid] $fn $xid)

open Lean PrettyPrinter Delaborator SubExpr in
/-- Remove the final component argument `j` from `body j`. Do not produce a bare
identifier, since that form deliberately keeps scalar elaboration. -/
private def etaGradientBody (j : Ident) (body : Term) : Option Term := do
  let `($f $args*) := body | failure
  if args.isEmpty then failure
  let y := args.back!
  if !y.raw.isIdent || y.raw.getId != j.getId then failure
  let args := args.pop
  let result := Syntax.mkApp f args
  match result with
  | `($_f:ident) => none
  | _ => some result

open Lean PrettyPrinter Delaborator SubExpr in
/-- Infoview: collapse the componentwise expansion `fun j ↦ ∇[x] body j` back to the
vector-valued notation `∇[x] body`; likewise for `∇[x = p]`. Other lambdas keep the
built-in rendering. -/
@[delab lam]
meta def delabGradientVector : Delab := whenNotPPOption getPPExplicit do
  let stx ← delabLam
  match stx with
  | `(fun $j:ident ↦ ∇[$x:ident] $body) =>
    match etaGradientBody j body with
    | some body =>
      match body with
      | `(Function.softmax $arg) => `(∇[$x] ($arg).$(mkIdent `softmax))
      | _ => `(∇[$x] $body)
    | none => pure stx
  | `(fun $j:ident ↦ ∇[$x:ident = $p] $body) =>
    match etaGradientBody j body with
    | some body =>
      match body with
      | `(Function.softmax $arg) => `(∇[$x = $p] ($arg).$(mkIdent `softmax))
      | _ => `(∇[$x = $p] $body)
    | none => pure stx
  | _ => pure stx
