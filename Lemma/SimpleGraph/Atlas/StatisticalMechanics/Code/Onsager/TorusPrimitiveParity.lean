import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveParity
open StatMech StatMech.Onsager


/--
[ons_dartEdgeSet_evenSubgraph_of_site_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveParity.lean)
-/
@[path]
private lemma ons_dartEdgeSet_evenSubgraph_of_site_injective_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2) :
-- imply
  ons_dartEdgeSet v ∈ StatMech.Ising.evenSubgraphs (onsTorusGraph L) := by
-- proof
  apply StatMech.Onsager.ons_dartEdgeSet_evenSubgraph_of_site_injective v hvalid hsite hnu

/--
[ons_simpleLoop_horizontal_winding_eq_zero_or_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveParity.lean)
-/
@[path]
private lemma ons_simpleLoop_horizontal_winding_eq_zero_or_odd_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx : ℤ}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (v k).2) = 0) :
-- imply
  mx = 0 ∨ Odd mx := by
-- proof
  apply StatMech.Onsager.ons_simpleLoop_horizontal_winding_eq_zero_or_odd v hvalid hsite hnu mx hmx hmy

/--
[ons_simpleLoop_horizontal_winding_odd_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/TorusPrimitiveParity.lean)
-/
@[path]
private lemma ons_simpleLoop_horizontal_winding_odd_of_ne_zero_eq
  {L n : ℕ}
  [Fact (2 < L)]
  [NeZero n]
  {v : Fin n → ons_Dart L}
  {mx : ℤ}
-- given
  (hvalid : ∀ k : Fin n, (v k).1 = ons_dirStep L (v (k + 1)).2 (v (k + 1)).1)
  (hsite : Function.Injective (fun k ↦ (v k).1))
  (hnu : ∀ k : Fin n, (v k).2 ≠ (v (k + 1)).2 + 2)
  (hmx : (∑ k, ons_dirExponentX (v k).2) = (L : ℤ) * mx)
  (hmy : (∑ k, ons_dirExponentY (v k).2) = 0)
  (hmx0 : mx ≠ 0) :
-- imply
  Odd mx := by
-- proof
  apply StatMech.Onsager.ons_simpleLoop_horizontal_winding_odd_of_ne_zero v hvalid hsite hnu mx hmx hmy hmx0


-- created on 2026-10-23
