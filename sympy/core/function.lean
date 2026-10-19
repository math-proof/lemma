import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Nat.Basic
import stdlib.List

/-- sympy `Difference(f(x), (x, n))`: the `n`-th forward difference with unit step, realized by Mathlib's `fwdDiff 1` iterated `n` times. -/
abbrev Difference {M G : Type*} [AddCommMonoid M] [One M] [AddCommGroup G] (f : M → G) (n : ℕ) : M → G :=
  (fwdDiff (1 : M))^[n] f

/--
[sympy.Subs](https://github.com/sympy/sympy/blob/master/sympy/core/function.py)

Unevaluated substitution: `Subst (fun x ↦ expr) x₀` is `expr` with `x := x₀`, written with the sugar
`Subst (expr | x = x₀)` (sympy `Subs(expr, x, x0)`).

Several variables are substituted *simultaneously* (sympy `Subs(expr, (x, y), (x0, y0))`):
`Subst (expr | x = x₀ ∧ y = y₀)` is `Subst (fun x y ↦ expr) x₀ y₀`, i.e. `(fun x y ↦ expr) x₀ y₀`, so the
values `x₀, y₀` are elaborated outside the binders (a free `x` in `y₀` is *not* replaced by `x₀`).
As in the `ℙ[π](… | x = u ∧ y = v)` sugar, `∧` joins the point equalities. Each value is parsed at
`term:36`, just above `∧` (`infixr:35`), so `Subst (f x y | x = n + 1 ∧ y = -2)` needs no parentheses,
while a value containing `∧`, `∨`, `→`, `↔` (or `fun`/`let` …) must be parenthesized. A relation inside a
value binds into the value: `Subst (p x | x = a = b)` substitutes the proposition `a = b` for `x`.

`Subst` is reducible, so `Subst f a = f a` holds by `rfl`; `simp` unfolds it via `Subst.eq_app`.

`Subst` is a keyword (so that `Subst (… | …)` parses): the constant itself is `«Subst»`, and both
`Subst (expr | x = x₀)` and the plain application `Subst f x₀` are accepted. Dotted names such as
`Subst.eq_app` are unaffected. In the sugar the body is a full term ending at the first top-level `|`,
so a body containing a bare `|` (e.g. a `match` alternative) must be parenthesized; `|x|` (abs),
`ℙ[π](… | …)` and `𝔼[…](… | …)` are self-delimited and need no parentheses.
-/
abbrev «Subst» {α : Sort*} {β : Sort*} (f : α → β) (a : α) : β :=
  f a

@[simp]
theorem Subst.eq_app {α : Sort*} {β : Sort*} (f : α → β) (a : α) : «Subst» f a = f a :=
  rfl

/-- One substitution `x = x₀` in the `Subst` sugar. -/
syntax substBinding := ident ppHardSpace "=" ppHardSpace term:36

/-- `Subst (expr | x = x₀ ∧ y = y₀)`: simultaneous substitution `x := x₀`, `y := y₀` in `expr`. -/
syntax:max (name := substSugar) "Subst" ppHardSpace "(" term ppHardSpace "|" ppSpace sepBy1(substBinding, " ∧ ") ")" : term

/-- `Subst f x₀ …`: plain application of the constant `«Subst»` (the name `Subst` is a keyword). -/
syntax:max (name := substApp) "Subst" (ppSpace colGt term:max)+ : term

macro_rules
  | `(Subst ($body | $bs∧*)) => do
    let bs := bs.getElems
    let xs ← bs.mapM fun
      | `(substBinding| $x:ident = $_) => pure x
      | _ => Lean.Macro.throwUnsupported
    let vs ← bs.mapM fun
      | `(substBinding| $_:ident = $v) => pure v
      | _ => Lean.Macro.throwUnsupported
    -- with `n` values, `Subst f x₀ : β` is applied to `n - 1` more: fix `β := _ → ⋯ → _` up front so the
    -- application elaborates before `f` does
    let mut β ← `(_)
    -- avoid `vs[1:]` (parsed as open-slice once stdlib.List is imported)
    for _ in vs.extract 1 vs.size do
      β ← `(_ → $β)
    `(«Subst» (β := $β) (fun $xs* ↦ $body) $vs*)

macro_rules
  | `(Subst $args*) => `(«Subst» $args*)

/-- Infoview: `Subst (fun x y ↦ expr) x₀ y₀` ↦ `Subst (expr | x = x₀ ∧ y = y₀)`; any other
application is shown as `Subst f …`. -/
@[app_unexpander «Subst»]
def Subst.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $vs*) => do
    -- the delaborated lambda is not yet parenthesized here
    if let `(fun $xs:ident* ↦ $body) := f then
      if xs.size == vs.size then
        let bs ← (xs.zip vs).mapM fun (x, v) => `(substBinding| $x:ident = $v)
        return ← `(Subst ($body | $bs∧*))
    `(Subst $f $vs*)
  | _ => throw ()


/-!
# Fun (py `sympy.tensor.indexed.Indexed`)

Parameter-indexed map: `f[i]` is the index; juxta after is a normal call on the residual.
For time-indexed trajectories `r : Fun ℕ (Ω → α)`, also `r[t:]` (open slice) via
`Fun.getSliceFrom`, matching bare `ℕ → α` sequences.

Notation `r[t:]` is elaborated below (needs `stdlib.List` for the shared open-slice syntax).
Kept in this file so there is a single import for both the structure and the sugar.
-/

/-- Parameter-indexed map: `f[i]` is the index; juxta after is a normal call on the residual.
For time-indexed trajectories `r : Fun ℕ (Ω → α)`, also `r[t:]` via
`Fun.getSliceFrom`, matching bare `ℕ → α` sequences. -/
structure Fun (ι : Type _) (α : Type _) where
  toFun : ι → α

/-- Type sugar: `ℕ ⇀ ℝ` means `Fun ℕ ℝ` (same precedence as `→`).
Semantic indexed-→ / function arrow (⇀, LaTeX \rightharpoonup). -/
infixr:25 " ⇀ " => Fun

namespace Fun

instance : CoeFun (Fun ι α) (fun _ => ι → α) where
  coe := toFun

instance : GetElem (Fun ι α) ι α (fun _ _ => True) where
  getElem f i _ := f.toFun i

@[simp] theorem getElem_eq (f : Fun ι α) (i : ι) : f[i] = f.toFun i := rfl
@[simp] theorem coe_eq (f : Fun ι α) (i : ι) : f i = f.toFun i := rfl

/-- Open-ended path slice: `r[t:]` for `r : Fun ℕ α` is `k ↦ r.toFun (t + k)`,
same shape as `Function.getSliceFrom` on bare sequences (so `@` / Dot keep working). -/
def getSliceFrom (f : Fun ℕ α) (t : ℕ) : ℕ → α :=
  fun k ↦ f.toFun (t + k)

@[simp]
theorem getSliceFrom_apply (f : Fun ℕ α) (t k : ℕ) :
    getSliceFrom f t k = f.toFun (t + k) := rfl

theorem getSliceFrom_def (f : Fun ℕ α) (t : ℕ) :
    getSliceFrom f t = fun k ↦ f.toFun (t + k) := rfl

end Fun

open Lean Elab Term Meta in
/-- `r[t:]` when `r : Fun ℕ _` → `Fun.getSliceFrom r t`.
Otherwise `throwUnsupportedSyntax` so `stdlib.List`'s elaborator handles bare `ℕ → α` / lists. -/
@[term_elab «term__[_:]»]
def Fun.elabGetSliceFrom : TermElab := fun stx expectedType? =>
  match stx with
  | `($x[$start :]) => do
    let saved ← saveState
    let ty? ← try
        let e ← withoutErrToSorry <| elabTerm x none
        pure (some (← whnfR (← instantiateMVars (← inferType e))))
      catch _ => pure none
    saved.restore
    let isFun := match ty? with
      | some (.app (.app (.const n _) d) _) =>
          n == ``Fun && d.isConstOf ``Nat
      | _ => false
    unless isFun do throwUnsupportedSyntax
    elabTerm (← `(Fun.getSliceFrom $x ($start))) expectedType?
  | _ => throwUnsupportedSyntax

open Lean Elab Term Meta in
/-- `f[i]` when `f : Fun ι α`: elaborate the index at type `ι`.
`GetElem`'s `idx` is not an outParam, so under binders like `sup[t] |δ[t]| < ∞`
(where `t` starts as a metavariable) the default `getElem` / `get_elem_tactic`
path fails with "failed to prove index is valid". Non-`Fun` collections
`throwUnsupportedSyntax` so Array/List GetElem stay unchanged. -/
elab_rules : term
  | `(getElem $x $i $_) => do
    let saved ← saveState
    let funData? ← try
        let xE ← withoutErrToSorry <| elabTerm x none
        let ty ← whnfR (← instantiateMVars (← inferType xE))
        match ty with
        | .app (.app (.const n _) ι) _ =>
            if n == ``Fun then pure (some (xE, ι)) else pure none
        | _ => pure none
      catch _ =>
        pure none
    let some (xE, ι) := funData? | do
      saved.restore
      throwUnsupportedSyntax
    let iE ← elabTermEnsuringType i ι
    -- defeq to `getElem x i trivial` via `Fun.getElem_eq`
    mkAppM ``Fun.toFun #[xE, iE]

namespace Fun

/-- Infoview: print `Fun.getSliceFrom r t` as `r[t:]`. -/
@[app_unexpander getSliceFrom]
def getSliceFrom.unexpand : Lean.PrettyPrinter.Unexpander
  | `($_ $f $t) => `($f[$t :])
  | `($_ $f $t $k) => `($f[$t :] $k)
  | _ => throw ()

@[simp]
theorem getSliceFrom_apply_notation (f : Fun ℕ α) (t k : ℕ) :
    f[t:] k = f.toFun (t + k) := rfl

theorem getSliceFrom_def_notation (f : Fun ℕ α) (t : ℕ) :
    f[t:] = fun k ↦ f.toFun (t + k) := rfl

@[simp]
theorem getSliceFrom_eq_function (f : Fun ℕ α) (t : ℕ) :
    getSliceFrom f t = Function.getSliceFrom f.toFun t := rfl

end Fun
