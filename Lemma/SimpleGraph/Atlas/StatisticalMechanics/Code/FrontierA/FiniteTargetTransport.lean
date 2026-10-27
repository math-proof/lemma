import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteTargetTransport
open Set StatMech StatMech.FrontierA


/--
[finiteTargetTransport_outside](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteTargetTransport.lean)
-/
@[path]
private lemma finiteTargetTransport_outside_eq
  {C : Set alpha}
  {N : Finset alpha}
  {x : alpha}
  {y : alpha}
-- given
  (hx : x ∉ C) :
-- imply
  finiteTargetTransport C N x y = 0 := by
-- proof
  apply StatMech.FrontierA.finiteTargetTransport_outside C N hx y

/--
[finiteTargetTransport_outgoing_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteTargetTransport.lean)
-/
@[path]
private lemma finiteTargetTransport_outgoing_eq_one_eq
  {C : Set alpha}
  {N : Finset alpha}
  {x : alpha}
-- given
  (hN : N.Nonempty)
  (hx : x ∈ C) :
-- imply
  ∑' y : alpha, finiteTargetTransport C N x y = 1 := by
-- proof
  apply StatMech.FrontierA.finiteTargetTransport_outgoing_eq_one C N hN hx

/--
[finiteTargetTransport_outgoing_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteTargetTransport.lean)
-/
@[path]
private lemma finiteTargetTransport_outgoing_le_one_eq
  {C : Set alpha}
  {N : Finset alpha}
  {x : alpha} :
-- imply
  ∑' y : alpha, finiteTargetTransport C N x y ≤ 1 := by
-- proof
  apply StatMech.FrontierA.finiteTargetTransport_outgoing_le_one C N x

/--
[finiteTargetTransport_incoming_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteTargetTransport.lean)
-/
@[path]
private lemma finiteTargetTransport_incoming_eq_top_eq
  {C : Set alpha}
  {N : Finset alpha}
  {y : alpha}
-- given
  (hC : C.Infinite)
  (_hN : N.Nonempty)
  (hy : y ∈ N) :
-- imply
  ∑' x : alpha, finiteTargetTransport C N x y = ⊤ := by
-- proof
  apply StatMech.FrontierA.finiteTargetTransport_incoming_eq_top C N hC _hN hy

/--
[finiteTargetTransport_image](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FiniteTargetTransport.lean)
-/
@[path]
private lemma finiteTargetTransport_image_eq
  [DecidableEq beta]
  {f : alpha → beta}
  {C : Set alpha}
  {N : Finset alpha}
  {x y : alpha}
-- given
  (hf : Function.Injective f) :
-- imply
  finiteTargetTransport (f '' C) (N.image f) (f x) (f y) = finiteTargetTransport C N x y := by
-- proof
  apply StatMech.FrontierA.finiteTargetTransport_image f hf C N x y


-- created on 2026-10-23
