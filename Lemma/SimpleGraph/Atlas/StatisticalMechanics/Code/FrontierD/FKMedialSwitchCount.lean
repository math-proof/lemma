import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialSwitchCount
open SimpleGraph Set StatMech StatMech.FrontierD


/--
[card_components_twoEdgeSwitch_le_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialSwitchCount.lean)
-/
@[path]
private lemma card_components_twoEdgeSwitch_le_add_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b c d : V}
-- given
  (heven : ∀ x, Even (G.degree x))
  (hab : G.Adj a b) :
-- imply
  let H := (G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent + 1 := by
-- proof
  apply StatMech.FrontierD.card_components_twoEdgeSwitch_le_add_one G heven hab

/--
[card_components_twoEdgeSwitch_of_not_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKMedialSwitchCount.lean)
-/
@[path]
private lemma card_components_twoEdgeSwitch_of_not_reachable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b c d : V}
-- given
  (heven : ∀ x, Even (G.degree x))
  (hab : G.Adj a b)
  (hcd : G.Adj c d)
  (hdisc : ¬ G.Reachable a c) :
-- imply
  let H := (G.deleteEdges {s(a, b), s(c, d)} ⊔ edge a d) ⊔ edge c b Nat.card H.ConnectedComponent + 1 = Nat.card G.ConnectedComponent := by
-- proof
  apply StatMech.FrontierD.card_components_twoEdgeSwitch_of_not_reachable G heven hab hcd hdisc


-- created on 2026-10-23
