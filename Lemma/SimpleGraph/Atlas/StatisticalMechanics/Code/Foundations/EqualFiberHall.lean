import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.EqualFiberHall
open Finset Fintype


/--
[hall_equalFiber_iff_card_fibers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/EqualFiberHall.lean)
-/
@[path]
private lemma hall_equalFiber_iff_card_fibers_eq
  [Fintype A]
  [Fintype B]
  [DecidableEq K]
-- given
  (f : A -> K)
  (g : B -> K) :
-- imply
  (forall S : Finset A, S.card <= (Finset.univ.filter fun b => exists a, a ∈ S /\ f a = g b).card) <-> forall k : K, Fintype.card {a : A // f a = k} <= Fintype.card {b : B // g b = k} := by
-- proof
  apply Fintype.hall_equalFiber_iff_card_fibers f g


-- created on 2026-10-23
