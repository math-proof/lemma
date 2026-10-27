import Mathlib.Tactic
import Lemma.Bool.Or.of.Or.Imp
import Lemma.Bool.And.of.And.Imp
import Lemma.Bool.Imp.is.ImpNotS
import Lemma.Bool.Imp.of.Imp.Imp
import Def.Lean.Meta.Expr.Part4 -- using Lean.Expr.is_Prop
import Def.Lean.FVarId
import Def.Tactic.Logic.Part3
open Lean Elab.Tactic Meta Parser.Tactic


/--
Syntax for `denote` tactic:
- extract the left hand side of the given hypothesis h
  - denote h_t : t = h.left
  - denote h_t : h.left = t

- extract the right hand side of the given hypothesis h
  - denote h_t : t = h.right
  - denote h_t : h.right = t

- extract the left hand side of the main goal
  - denote h_t : t = left
  - denote h_t : left = t

- extract the right hand side of the main goal
  - denote h_t : t = right
  - denote h_t : right = t

- extract the left `let-binding` (which is the `let expression`) of the main goal
  - denote h_t : t = _
  - denote h_t : _ = t

wherein:
* h   is the name of an existing hypothesis h : A = B (an equality)
* t   is the new name for the right‐hand side of h
* h_t is the name for the new hypothesis t = h.right
-/
syntax (name := denote) "denote" ident ":" term:51 "=" term : tactic

