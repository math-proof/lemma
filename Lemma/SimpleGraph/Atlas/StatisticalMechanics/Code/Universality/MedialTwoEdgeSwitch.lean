import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.MedialTwoEdgeSwitch
open SimpleGraph Set StatMech StatMech.Universality


/--
[medialTwoEdgeSwitch_swap_pairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MedialTwoEdgeSwitch.lean)
-/
@[path]
private lemma medialTwoEdgeSwitch_swap_pairs_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b c d : V} :
-- imply
  medialTwoEdgeSwitch G c d a b = medialTwoEdgeSwitch G a b c d := by
-- proof
  apply StatMech.Universality.medialTwoEdgeSwitch_swap_pairs G a b c d

/--
[medialTwoEdgeSwitch_reachable_all_of_reachable_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MedialTwoEdgeSwitch.lean)
-/
@[path]
private lemma medialTwoEdgeSwitch_reachable_all_of_reachable_left_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b c d x : V}
-- given
  (heven : forall x, Even (G.degree x))
  (hab : G.Adj a b)
  (hcd : G.Adj c d)
  (hdisc : ¬ G.Reachable a c)
  (hxa : G.Reachable x a) :
-- imply
  (medialTwoEdgeSwitch G a b c d).Reachable x a ∧ (medialTwoEdgeSwitch G a b c d).Reachable x b ∧ (medialTwoEdgeSwitch G a b c d).Reachable x c ∧ (medialTwoEdgeSwitch G a b c d).Reachable x d := by
-- proof
  apply StatMech.Universality.medialTwoEdgeSwitch_reachable_all_of_reachable_left G heven hab hcd hdisc hxa

/--
[medialTwoEdgeSwitch_reachable_all_of_reachable_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MedialTwoEdgeSwitch.lean)
-/
@[path]
private lemma medialTwoEdgeSwitch_reachable_all_of_reachable_right_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b c d x : V}
-- given
  (heven : forall x, Even (G.degree x))
  (hab : G.Adj a b)
  (hcd : G.Adj c d)
  (hdisc : ¬ G.Reachable a c)
  (hxc : G.Reachable x c) :
-- imply
  (medialTwoEdgeSwitch G a b c d).Reachable x a ∧ (medialTwoEdgeSwitch G a b c d).Reachable x b ∧ (medialTwoEdgeSwitch G a b c d).Reachable x c ∧ (medialTwoEdgeSwitch G a b c d).Reachable x d := by
-- proof
  apply StatMech.Universality.medialTwoEdgeSwitch_reachable_all_of_reachable_right G heven hab hcd hdisc hxc

/--
[medialTwoEdgeSwitch_reachable_iff_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/MedialTwoEdgeSwitch.lean)
-/
@[path]
private lemma medialTwoEdgeSwitch_reachable_iff_of_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {a b c d x y : V}
-- given
  (hab : G.Adj a b)
  (hcd : G.Adj c d)
  (hxa : ¬ G.Reachable x a)
  (hxc : ¬ G.Reachable x c) :
-- imply
  (medialTwoEdgeSwitch G a b c d).Reachable x y ↔ G.Reachable x y := by
-- proof
  apply StatMech.Universality.medialTwoEdgeSwitch_reachable_iff_of_disjoint G hab hcd hxa hxc


-- created on 2026-10-23
