import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Def.Order.ExprWithLimits.Part2


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


