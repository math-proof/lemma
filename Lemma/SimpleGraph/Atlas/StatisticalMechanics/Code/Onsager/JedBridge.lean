import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.JedBridge
open StatMech StatMech.Onsager StatMech.Onsager.JedBridge


/--
[posSite_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma posSite_zero_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {i : Fin (m + 3)} :
-- imply
  (posSite d i) 0 = (pos d i).1 := by
-- proof
  apply StatMech.Onsager.JedBridge.posSite_zero d i

/--
[posSite_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma posSite_one_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  {i : Fin (m + 3)} :
-- imply
  (posSite d i) 1 = (pos d i).2 := by
-- proof
  apply StatMech.Onsager.JedBridge.posSite_one d i

/--
[posSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma posSite_injective_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hsimple : Function.Injective (pos d)) :
-- imply
  Function.Injective (posSite d) := by
-- proof
  apply StatMech.Onsager.JedBridge.posSite_injective d hsimple

/--
[stepOf_natAbs_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma stepOf_natAbs_sum_eq
  {w : Fin 4} :
-- imply
  (stepOf w).1.natAbs + (stepOf w).2.natAbs = 1 := by
-- proof
  apply StatMech.Onsager.JedBridge.stepOf_natAbs_sum w

/--
[walk_isSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma walk_isSub_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
  ⦃i j : Fin (m + 3)⦄
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hadj : (cycleGraph (m + 3)).Adj i j) :
-- imply
  (hypercubicLattice 2).Adj (posSite d i) (posSite d j) := by
-- proof
  apply StatMech.Onsager.JedBridge.walk_isSub d hclosed hadj

/--
[cycleGraph_card_components_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma cycleGraph_card_components_one_eq
  {m : ℕ} :
-- imply
  Nat.card (cycleGraph (m + 3)).ConnectedComponent = 1 := by
-- proof
  apply StatMech.Onsager.JedBridge.cycleGraph_card_components_one m

/--
[cycleGraph_card_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma cycleGraph_card_edges_eq
  {m : ℕ} :
-- imply
  (cycleGraph (m + 3)).edgeSet.ncard = m + 3 := by
-- proof
  apply StatMech.Onsager.JedBridge.cycleGraph_card_edges m

/--
[cycle_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma cycle_nullity_one_eq
  {m : ℕ} :
-- imply
  nullity (cycleGraph (m + 3)) = 1 := by
-- proof
  apply StatMech.Onsager.JedBridge.cycle_nullity_one m

/--
[walkSubgraph_nullity_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma walkSubgraph_nullity_one_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  nullity (walkSubgraph d hclosed hsimple).G = 1 := by
-- proof
  apply StatMech.Onsager.JedBridge.walkSubgraph_nullity_one d hclosed hsimple

/--
[walk_one_bounded_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma walk_one_bounded_region_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  Nat.card {c : (whb_faceRegion (imageGraph (walkSubgraph d hclosed hsimple))).ConnectedComponent // c.supp.Finite} = 1 := by
-- proof
  apply StatMech.Onsager.JedBridge.walk_one_bounded_region d hclosed hsimple

/--
[walk_faithfulRegionCount_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/JedBridge.lean)
-/
@[path]
private lemma walk_faithfulRegionCount_one_eq
  {m : ℕ}
  {d : Fin (m + 3) → Fin 4}
-- given
  (hclosed : ∑ i, stepOf (d i) = 0)
  (hsimple : Function.Injective (pos d)) :
-- imply
  whc_faithfulRegionCount (walkSubgraph d hclosed hsimple) = 1 := by
-- proof
  apply StatMech.Onsager.JedBridge.walk_faithfulRegionCount_one d hclosed hsimple


-- created on 2026-10-23
