import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Def.Order.ExprWithLimits


/--
Argmax / argmin big operators, written like `max[i] e` (see `Macro/Order/Max.lean`):

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

