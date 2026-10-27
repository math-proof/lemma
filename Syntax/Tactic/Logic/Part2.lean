import Mathlib.Tactic
import Lemma.Bool.Or.of.Or.Imp
import Lemma.Bool.And.of.And.Imp
import Lemma.Bool.Imp.is.ImpNotS
import Lemma.Bool.Imp.of.Imp.Imp
import Def.Lean.Meta.Expr.Part4 -- using Lean.Expr.is_Prop
import Def.Lean.FVarId
import Def.Tactic.Logic.Part2
open Lean Elab.Tactic Meta Parser.Tactic


/--
`mpr` tactic tries to employ modus ponens reverse using the given hypothesis.
The hypothesis must be of the form `h₀ : p → q`
- if modifier h₁ is present, h₁ must contain `q` which resides in the negation part, The tactic replaces `q` with `p` at the local hypothesis h₁
- if modifier h₁ isn't present, the goal must contain `q`. The tactic replaces `q` in the goal with `p`
-/
syntax (name := mpr) "mpr" "[" term,+ "]" (location)? : tactic

