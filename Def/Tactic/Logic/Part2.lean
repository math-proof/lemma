import Mathlib.Tactic
import Lemma.Bool.Or.of.Or.Imp
import Lemma.Bool.And.of.And.Imp
import Lemma.Bool.Imp.is.ImpNotS
import Lemma.Bool.Imp.of.Imp.Imp
import Def.Lean.Meta.Expr.Part4 -- using Lean.Expr.is_Prop
import Def.Lean.FVarId
import Syntax.Tactic.Logic
open Lean Elab.Tactic Meta Parser.Tactic


@[tactic mp]
def evalMp : Tactic
| `(tactic| mp [ $[ $h₀ ],* ] $[$loc:location]?) => employModusPonens `mp h₀ loc false
| _ => throwError "Usage: mp [ <term>,+ ] at <location>?"


