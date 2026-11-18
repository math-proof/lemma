module

public import Mathlib.Tactic
public import Theorem.Bool.Or.of.Or.Imp
public import Theorem.Bool.And.of.And.Imp
public import Theorem.Bool.Imp.is.ImpNotS
public import Theorem.Bool.Imp.of.Imp.Imp
public import Def.Lean.Meta.Expr -- using Lean.Expr.is_Prop
public import Def.Lean.FVarId
public import Def.Tactic.Logic.Part2

public meta section

open Lean Elab.Tactic Meta Parser.Tactic


/--
`mpr` tactic tries to employ modus ponens reverse using the given hypothesis.
The hypothesis must be of the form `h₀ : p → q`
- if modifier h₁ is present, h₁ must contain `q` which resides in the negation part, The tactic replaces `q` with `p` at the local hypothesis h₁
- if modifier h₁ isn't present, the goal must contain `q`. The tactic replaces `q` in the goal with `p`
-/
syntax (name := mpr) "mpr" "[" term,+ "]" (location)? : tactic

