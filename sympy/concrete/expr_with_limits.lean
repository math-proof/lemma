import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-- `Minima[x:S](f(x))`: the infimum of `f` over `S`. -/
noncomputable def Minima [InfSet β] (S : Set α) (f : α → β) : β :=
  sInf (f '' S)

/-- `Maxima[x:S](f(x))`: the supremum of `f` over `S`. -/
noncomputable def Maxima [SupSet β] (S : Set α) (f : α → β) : β :=
  sSup (f '' S)

/-- Underlying argmin: some minimizer of `f` on `S` (arbitrary when none exists).
Prefer the big-operator sugar `min⁻¹[i] e` / `min⁻¹[x ∈ S] e`. -/
noncomputable def «min⁻¹» [Nonempty α] [Preorder β] (S : Set α) (f : α → β) : α :=
  Classical.epsilon fun x => x ∈ S ∧ ∀ y ∈ S, f x ≤ f y

/-- Underlying argmax: some maximizer of `f` on `S` (arbitrary when none exists).
Prefer the big-operator sugar `max⁻¹[i] e` / `max⁻¹[x ∈ S] e`. -/
noncomputable def «max⁻¹» [Nonempty α] [Preorder β] (S : Set α) (f : α → β) : α :=
  Classical.epsilon fun x => x ∈ S ∧ ∀ y ∈ S, f y ≤ f x

/--
Argmax / argmin big operators, written like `max[i] e` (see `sympy/concrete/max.lean`):

* `max⁻¹[i] e` / `min⁻¹[i] e` — over `Set.univ`
* `max⁻¹[i : T] e` — typed binder
* `max⁻¹[i | p] e` / `max⁻¹[i : T | p] e` — over `{i | p}`
* `max⁻¹[x ∈ S] e` / `min⁻¹[x ∈ S] e` — over an arbitrary set `S`
* `max⁻¹[a, b] e` nests as `max⁻¹[a] (max⁻¹[b] e)` (same as `max`)

The body is parsed at precedence 67 (like `∑` / `max`).
-/
syntax argExtBinder := ("(" ident " : " term ")") <|> (ident (" : " term)?)

syntax:67 (name := maxInvVal) "max⁻¹[" sepBy1(argExtBinder, ", ") (" : " term)? "] " term:67 : term
syntax:67 (name := minInvVal) "min⁻¹[" sepBy1(argExtBinder, ", ") (" : " term)? "] " term:67 : term
syntax:67 (name := maxInvFilter) "max⁻¹[" sepBy1(argExtBinder, ", ") " | " term "] " term:67 : term
syntax:67 (name := minInvFilter) "min⁻¹[" sepBy1(argExtBinder, ", ") " | " term "] " term:67 : term
syntax:67 (name := maxInvMem) "max⁻¹[" ident " ∈ " term "] " term:67 : term
syntax:67 (name := minInvMem) "min⁻¹[" ident " ∈ " term "] " term:67 : term

open Lean in
private def parseArgExtBinder (stx : TSyntax `argExtBinder) :
    MacroM (TSyntax `ident × Option (TSyntax `term)) := do
  let g := stx.raw[0]
  let args := g.getArgs
  if args.size == 5 then
    pure (⟨args[1]!⟩, some ⟨args[3]!⟩)
  else if args.size == 2 then
    let x : TSyntax `ident := ⟨args[0]!⟩
    let opt := args[1]!
    if opt.getArgs.isEmpty then
      pure (x, none)
    else
      pure (x, some ⟨opt[1]!⟩)
  else
    Macro.throwErrorAt stx "expected binder `x`, `x : T`, or `(x : T)`"

open Lean in
macro_rules
  | `(max⁻¹[$xs:argExtBinder,*] $e) => do
    let binders ← xs.getElems.mapM parseArgExtBinder
    let mut r : TSyntax `term := e
    for (x, ty?) in binders.reverse do
      r ← match ty? with
        | some ty => `(«max⁻¹» (Set.univ : Set $ty) (fun ($x:ident : $ty) => $r))
        | none => `(«max⁻¹» Set.univ (fun $x:ident => $r))
    pure r
  | `(max⁻¹[$xs:argExtBinder,* : $T] $e) => do
    let binders ← xs.getElems.mapM parseArgExtBinder
    let mut r : TSyntax `term := e
    for (x, ty?) in binders.reverse do
      let ty := ty?.getD T
      r ← `(«max⁻¹» (Set.univ : Set $ty) (fun ($x:ident : $ty) => $r))
    pure r
  | `(min⁻¹[$xs:argExtBinder,*] $e) => do
    let binders ← xs.getElems.mapM parseArgExtBinder
    let mut r : TSyntax `term := e
    for (x, ty?) in binders.reverse do
      r ← match ty? with
        | some ty => `(«min⁻¹» (Set.univ : Set $ty) (fun ($x:ident : $ty) => $r))
        | none => `(«min⁻¹» Set.univ (fun $x:ident => $r))
    pure r
  | `(min⁻¹[$xs:argExtBinder,* : $T] $e) => do
    let binders ← xs.getElems.mapM parseArgExtBinder
    let mut r : TSyntax `term := e
    for (x, ty?) in binders.reverse do
      let ty := ty?.getD T
      r ← `(«min⁻¹» (Set.univ : Set $ty) (fun ($x:ident : $ty) => $r))
    pure r
  | `(max⁻¹[$xs:argExtBinder,* | $c] $e) => do
    let binders ← xs.getElems.mapM parseArgExtBinder
    if binders.size ≠ 1 then
      Macro.throwError "max⁻¹[… | …] currently supports a single binder"
    let (x, ty?) := binders[0]!
    match ty? with
    | some ty => `(«max⁻¹» (Set.ofPred fun ($x:ident : $ty) => $c) (fun ($x:ident : $ty) => $e))
    | none => `(«max⁻¹» (Set.ofPred fun $x:ident => $c) (fun $x:ident => $e))
  | `(min⁻¹[$xs:argExtBinder,* | $c] $e) => do
    let binders ← xs.getElems.mapM parseArgExtBinder
    if binders.size ≠ 1 then
      Macro.throwError "min⁻¹[… | …] currently supports a single binder"
    let (x, ty?) := binders[0]!
    match ty? with
    | some ty => `(«min⁻¹» (Set.ofPred fun ($x:ident : $ty) => $c) (fun ($x:ident : $ty) => $e))
    | none => `(«min⁻¹» (Set.ofPred fun $x:ident => $c) (fun $x:ident => $e))
  | `(max⁻¹[$x:ident ∈ $S] $e) => do
    -- eta-contract `max⁻¹[x ∈ S] f x` → `«max⁻¹» S f`
    match e with
    | `($f:ident $y:ident) =>
      if y.raw.getId == x.raw.getId then
        `(«max⁻¹» $S $f)
      else
        `(«max⁻¹» $S (fun $x:ident => $e))
    | _ => `(«max⁻¹» $S (fun $x:ident => $e))
  | `(min⁻¹[$x:ident ∈ $S] $e) => do
    match e with
    | `($f:ident $y:ident) =>
      if y.raw.getId == x.raw.getId then
        `(«min⁻¹» $S $f)
      else
        `(«min⁻¹» $S (fun $x:ident => $e))
    | _ => `(«min⁻¹» $S (fun $x:ident => $e))


-- created on 2026-09-27
