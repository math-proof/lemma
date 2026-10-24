import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.WindingBridge
open StatMech StatMech.Onsager StatMech.Onsager.WindingBridge


/--
[toSite_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma toSite_zero_eq
  {p : Pt} :
-- imply
  toSite p 0 = p.1 := by
-- proof
  apply StatMech.Onsager.WindingBridge.toSite_zero p

/--
[toSite_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma toSite_one_eq
  {p : Pt} :
-- imply
  toSite p 1 = p.2 := by
-- proof
  apply StatMech.Onsager.WindingBridge.toSite_one p

/--
[toSite_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma toSite_injective_eq :
-- imply
  Function.Injective toSite := by
-- proof
  apply StatMech.Onsager.WindingBridge.toSite_injective

/--
[shift_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma shift_injective_eq :
-- imply
  Function.Injective (fun p : Pt => (p.1 + 1, p.2)) := by
-- proof
  apply StatMech.Onsager.WindingBridge.shift_injective

/--
[toSite_adj_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma toSite_adj_shift_eq
  {p : Pt} :
-- imply
  (hypercubicLattice 2).Adj (toSite p) (toSite (p.1 + 1, p.2)) := by
-- proof
  apply StatMech.Onsager.WindingBridge.toSite_adj_shift p

/--
[barrier_of_side_change](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma barrier_of_side_change_eq
  {S : Set (Site 2)}
  {x y : Site 2}
-- given
  (hadj : (hypercubicLattice 2).Adj x y)
  (hchg : ¬ (x ∈ S ↔ y ∈ S)) :
-- imply
  bdEdge S s(x, y) := by
-- proof
  apply StatMech.Onsager.WindingBridge.barrier_of_side_change S hadj hchg

/--
[preS_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma preS_finite_eq
  {S : Set (Site 2)}
-- given
  (hfin : S.Finite) :
-- imply
  (preS S).Finite := by
-- proof
  apply StatMech.Onsager.WindingBridge.preS_finite S hfin

/--
[shiftPre_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma shiftPre_finite_eq
  {S : Set (Site 2)}
-- given
  (hfin : S.Finite) :
-- imply
  {p : Pt | toSite (p.1 + 1, p.2) ∈ S}.Finite := by
-- proof
  apply StatMech.Onsager.WindingBridge.shiftPre_finite S hfin

/--
[bset_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma bset_subset_eq
  {S : Set (Site 2)} :
-- imply
  Bset S ⊆ preS S ∪ {p : Pt | toSite (p.1 + 1, p.2) ∈ S} := by
-- proof
  apply StatMech.Onsager.WindingBridge.bset_subset S

/--
[bset_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma bset_finite_eq
  {S : Set (Site 2)}
-- given
  (hfin : S.Finite) :
-- imply
  (Bset S).Finite := by
-- proof
  apply StatMech.Onsager.WindingBridge.bset_finite S hfin

/--
[le_xBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma le_xBound_eq
  {S : Set (Site 2)}
  {x : Site 2}
-- given
  (hfin : S.Finite)
  (hx : x ∈ S) :
-- imply
  x 0 ≤ xBound S hfin := by
-- proof
  apply StatMech.Onsager.WindingBridge.le_xBound S hfin hx

/--
[boundedRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma boundedRight_eq
  {S : Set (Site 2)}
-- given
  (hfin : S.Finite) :
-- imply
  BoundedRight (mkBoxData S hfin) (preS S) := by
-- proof
  apply StatMech.Onsager.WindingBridge.boundedRight S hfin

/--
[boundaryCovers](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma boundaryCovers_eq
  {S : Set (Site 2)}
-- given
  (hfin : S.Finite) :
-- imply
  BoundaryCoversTransitions (mkBoxData S hfin) (preS S) := by
-- proof
  apply StatMech.Onsager.WindingBridge.boundaryCovers S hfin

/--
[interiorReaches_of_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma interiorReaches_of_cluster_eq
  {S : Set (Site 2)}
  {w : Pt}
-- given
  (hfin : S.Finite)
  (hin : toSite (rayX w 1) ∈ S) :
-- imply
  InteriorReaches (mkBoxData S hfin) w := by
-- proof
  apply StatMech.Onsager.WindingBridge.interiorReaches_of_cluster S hfin w hin

/--
[chord_of_cluster](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingBridge.lean)
-/
@[path]
private lemma chord_of_cluster_eq
  {S : Set (Site 2)}
  {w : Pt}
-- given
  (hfin : S.Finite)
  (hw : w ∈ (mkBoxData S hfin).B)
  (hin : toSite (rayX w 1) ∈ S) :
-- imply
  ∃ k : ℕ, 1 ≤ k ∧ rayX w k ∈ (mkBoxData S hfin).B ∧ (∀ j : ℕ, 1 ≤ j → j < k → rayX w j ∉ (mkBoxData S hfin).B) := by
-- proof
  apply StatMech.Onsager.WindingBridge.chord_of_cluster S hfin w hw hin


-- created on 2026-10-23
