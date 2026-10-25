import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopAnchoredCutInjective
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[multibondCut_eq_propagate_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCutInjective.lean)
-/
@[path]
private lemma multibondCut_eq_propagate_adj_eq
  [Fintype V]
  [DecidableEq V]
  {ends : P → V × V}
  {s t : V → Bool}
  {x y : V}
-- given
  (hcut : multibondCut ends s = multibondCut ends t)
  (hxy : (ons_multibondSupportGraph ends).Adj x y)
  (hx : s x = t x) :
-- imply
  s y = t y := by
-- proof
  apply StatMech.Onsager.multibondCut_eq_propagate_adj ends s t hcut hxy hx

/--
[multibondCut_eq_propagate_walk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCutInjective.lean)
-/
@[path]
private lemma multibondCut_eq_propagate_walk_eq
  [Fintype V]
  [DecidableEq V]
  {ends : P → V × V}
  {s t : V → Bool}
  {x y : V}
  {walk : (ons_multibondSupportGraph ends).Walk x y}
-- given
  (hcut : multibondCut ends s = multibondCut ends t)
  (hx : s x = t x) :
-- imply
  s y = t y := by
-- proof
  apply StatMech.Onsager.multibondCut_eq_propagate_walk ends s t hcut walk hx

/--
[multibondCut_anchored_injective_of_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCutInjective.lean)
-/
@[path]
private lemma multibondCut_anchored_injective_of_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {ends : P → V × V}
  {root : V}
-- given
  (hreach : ∀ v : V, (ons_multibondSupportGraph ends).Reachable root v) :
-- imply
  Function.Injective (fun config : AnchoredConfig V root => multibondCut ends config.1) := by
-- proof
  apply StatMech.Onsager.multibondCut_anchored_injective_of_reachable ends root hreach

/--
[multibondCut_anchored_injective_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopAnchoredCutInjective.lean)
-/
@[path]
private lemma multibondCut_anchored_injective_of_connected_eq
  [Fintype V]
  [DecidableEq V]
  {ends : P → V × V}
  {root : V}
-- given
  (hconnected : (ons_multibondSupportGraph ends).Connected) :
-- imply
  Function.Injective (fun config : AnchoredConfig V root => multibondCut ends config.1) := by
-- proof
  apply StatMech.Onsager.multibondCut_anchored_injective_of_connected ends root hconnected


-- created on 2026-10-23
