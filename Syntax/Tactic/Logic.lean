import Mathlib.Tactic
import Lemma.Bool.Or.of.Or.Imp
import Lemma.Bool.And.of.And.Imp
import Lemma.Bool.Imp.is.ImpNotS
import Lemma.Bool.Imp.of.Imp.Imp
import Def.Lean.Meta.Expr.Part4 -- using Lean.Expr.is_Prop
import Def.Lean.FVarId
import Def.Tactic.Logic
open Lean Elab.Tactic Meta Parser.Tactic


/--
`mp` tactic tries to employ modus ponens reverse using the given hypothesis.
The hypothesis must be of the form `h₀ : p → q`
- if modifier h₁ is present, h₁ must contain `p`, The tactic replaces `p` in the goal with `q` by applying `h`.
- if modifier h₁ isn't present, the goal must contain `p` which must reside in the negation part. The tactic replaces `p` in the goal with `q`
-/
syntax (name := mp) "mp" "[" term,+ "]" (location)? : tactic

