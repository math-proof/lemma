module

public import Mathlib.Tactic
public import Theorem.Bool.Or.of.Or.Imp
public import Theorem.Bool.And.of.And.Imp
public import Theorem.Bool.Imp.is.ImpNotS
public import Theorem.Bool.Imp.of.Imp.Imp
public import Def.Lean.Meta.Expr -- using Lean.Expr.is_Prop
public import Def.Lean.FVarId
public meta import Def.Tactic.Logic
public import Syntax.Tactic.Logic

@[expose] public section

open Lean Elab.Tactic Meta Parser.Tactic


@[tactic mp]
meta def evalMp : Tactic
| `(tactic| mp [ $[ $h₀ ],* ] $[$loc:location]?) => employModusPonens `mp h₀ loc false
| _ => throwError "Usage: mp [ <term>,+ ] at <location>?"
