import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitRankFiveRouting.Part2
open StatMech StatMech.Ising


/--
[lpReplicaCurrentFoldedEdge_isDiag_iff_exists_seam](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaCurrentFoldedEdge_isDiag_iff_exists_seam_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentFoldedEdge G sites e).IsDiag ↔ ∃ i, e.1 = lpReplicaCurrentSeamEdge sites i := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentFoldedEdge_isDiag_iff_exists_seam G sites e

/--
[lpReplicaCurrentLeft_mem_tripleSeamGhostSource_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaCurrentLeft_mem_tripleSeamGhostSource_iff_eq
  [Fintype V]
  [DecidableEq V]
  {i j k t : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  lpReplicaCurrentLeft sites t ∈ lpReplicaTripleSeamGhostSource sites i j k ↔ t = i ∨ t = j ∨ t = k := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentLeft_mem_tripleSeamGhostSource_iff sites hsite hij hik hjk

/--
[lpReplicaCurrentRight_mem_tripleSeamGhostSource_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaCurrentRight_mem_tripleSeamGhostSource_iff_eq
  [Fintype V]
  [DecidableEq V]
  {i j k t : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  lpReplicaCurrentRight sites t ∈ lpReplicaTripleSeamGhostSource sites i j k ↔ t = i ∨ t = j ∨ t = k := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentRight_mem_tripleSeamGhostSource_iff sites hsite hij hik hjk

/--
[lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : I}
  {x : V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  (.inl (.inl x) : LPReplicaCurrentVertex V) ∈ lpReplicaTripleSeamGhostSource sites i j k ↔ x = sites i ∨ x = sites j ∨ x = sites k := by
-- proof
  apply StatMech.Ising.lpReplicaPhysicalLeft_mem_tripleSeamGhostSource_iff sites hsite hij hik hjk x

/--
[lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : I}
  {x : V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k) :
-- imply
  (.inl (.inr x) : LPReplicaCurrentVertex V) ∈ lpReplicaTripleSeamGhostSource sites i j k ↔ x = sites i ∨ x = sites j ∨ x = sites k := by
-- proof
  apply StatMech.Ising.lpReplicaPhysicalRight_mem_tripleSeamGhostSource_iff sites hsite hij hik hjk x

/--
[lpReplicaCurrentFold_eq_site_of_mem_tripleSeamGhostSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaCurrentFold_eq_site_of_mem_tripleSeamGhostSource_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : I}
  {x : LPReplicaCurrentVertex V}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k)
  (hx : x ∈ lpReplicaTripleSeamGhostSource sites i j k)
  (hx0 : x ≠ lpReplicaCurrentGhost0)
  (hx1 : x ≠ lpReplicaCurrentGhost1) :
-- imply
  ∃ u, (u = i ∨ u = j ∨ u = k) ∧ lpReplicaCurrentFold x = Sum.inl (sites u) := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentFold_eq_site_of_mem_tripleSeamGhostSource sites hsite hij hik hjk x hx hx0 hx1

/--
[lpReplicaCurrentGhost0_mem_tripleSeamGhostSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaCurrentGhost0_mem_tripleSeamGhostSource_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : I}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∈ lpReplicaTripleSeamGhostSource sites i j k := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentGhost0_mem_tripleSeamGhostSource sites i j k

/--
[lpReplicaCurrentGhost1_mem_tripleSeamGhostSource](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaCurrentGhost1_mem_tripleSeamGhostSource_eq
  [Fintype V]
  [DecidableEq V]
  {i j k : I}
-- given
  (sites : I -> V) :
-- imply
  (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∈ lpReplicaTripleSeamGhostSource sites i j k := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentGhost1_mem_tripleSeamGhostSource sites i j k

/--
[lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j k : I}
  {K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hKcard : K.card = 4)
  (hsupport : K.biUnion (fun e => (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m e).toFinset) = lpReplicaTripleSeamGhostSource sites i j k)
  (hunique : ∀ x ∈ lpReplicaTripleSeamGhostSource sites i j k, ∃! e, e ∈ K ∧ x ∈ (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m e).toFinset)
  (hnoI : ∀ e ∈ K, e.1.1 ≠ lpReplicaCurrentSeamEdge sites i)
  (hnoJ : ∀ e ∈ K, e.1.1 ≠ lpReplicaCurrentSeamEdge sites j) :
-- imply
  ∃ e ∈ K, (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉ StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m e ∧ (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m e ∧ ¬ (lpReplicaCurrentFoldedEdge G sites e.1).IsDiag := by
-- proof
  apply StatMech.Ising.lpReplica_fourCopyTripleMatching_exists_strictPhysicalRoute G sites hsite hij hik hjk m K hKcard hsupport hunique hnoI hnoJ

/--
[lpReplica_strictPhysicalRoute_folded_labels](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplica_strictPhysicalRoute_folded_labels_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {i j k : I}
  {K : Finset (StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m)}
  {d : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) m}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hsupport : K.biUnion (fun e => (StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m e).toFinset) = lpReplicaTripleSeamGhostSource sites i j k)
  (hdK : d ∈ K)
  (hd0 : (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉ StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m d)
  (hd1 : (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) m d)
  (hddiag : ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag) :
-- imply
  ∃ u v, (u = i ∨ u = j ∨ u = k) ∧ (v = i ∨ v = j ∨ v = k) ∧ u ≠ v ∧ lpReplicaCurrentFoldedEdge G sites d.1 = s(Sum.inl (sites u), Sum.inl (sites v)) := by
-- proof
  apply StatMech.Ising.lpReplica_strictPhysicalRoute_folded_labels G sites hsite hij hik hjk m K hsupport d hdK hd0 hd1 hddiag

/--
[lpReplicaThirdOfThree_spec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaThirdOfThree_spec_eq
  [Fintype V]
  [DecidableEq V]
  {i j k u v : I}
-- given
  (hij : i ≠ j)
  (hik : i ≠ k)
  (hjk : j ≠ k)
  (hu : u = i ∨ u = j ∨ u = k)
  (hv : v = i ∨ v = j ∨ v = k)
  (huv : u ≠ v) :
-- imply
  let l := lpReplicaThirdOfThree i j k u v l ≠ u ∧ l ≠ v ∧ (l = i ∨ l = j ∨ l = k) := by
-- proof
  apply StatMech.Ising.lpReplicaThirdOfThree_spec hij hik hjk hu hv huv

/--
[lpReplicaCurrentEdge_toFinset_symmDiff_reflect_eq_seams](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaCurrentEdge_toFinset_symmDiff_reflect_eq_seams_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {e : (lpReplicaCurrentGraph G sites).edgeFinset}
  {u v : I}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (huv : u ≠ v)
  (hfold : lpReplicaCurrentFoldedEdge G sites e = s(Sum.inl (sites u), Sum.inl (sites v))) :
-- imply
  (Sym2.toFinset (e.1)) ∆ (Sym2.toFinset (Sym2.map lpReplicaCurrentReflect (e.1))) = lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) u ∆ lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) v := by
-- proof
  apply StatMech.Ising.lpReplicaCurrentEdge_toFinset_symmDiff_reflect_eq_seams G sites hsite e huv hfold

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictPhysicalRoute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictPhysicalRoute_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  let a := z.toAggregate G sites q let k := lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ∃ c d : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1, c.1.1 = lpReplicaCurrentSeamEdge sites k ∧ d ∈ Finset.univ \ {c} ∧ (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) ∉ StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧ (lpReplicaCurrentGhost1 : LPReplicaCurrentVertex V) ∉ StatMech.Sharpness.FluxEdgeCopy.endsM (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1 d ∧ ¬ (lpReplicaCurrentFoldedEdge G sites d.1).IsDiag := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_strictPhysicalRoute G sites hsite q hcard z

/--
[lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitRankFiveRouting.lean)
-/
@[path]
private lemma lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {z : LPReplicaAggregateUnmarkedSaturatedSourceRankFive G sites q}
-- given
  (sites : I -> V)
  (hsite : Function.Injective sites)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hcard : Fintype.card (LPReplicaOrbitCommonSlot G sites q) = 5) :
-- imply
  let a := z.toAggregate G sites q let k := lpReplicaAggregateDecoratedSourceSelectedSeam G sites hsite q a ∃ c d : StatMech.Sharpness.FluxEdgeCopy.Copy (lpReplicaCurrentGraph G sites) a.2.2.2.1.1.1, ∃ u v, c.1.1 = lpReplicaCurrentSeamEdge sites k ∧ d ∈ Finset.univ \ {c} ∧ (u = a.1 ∨ u = a.2.1 ∨ u = k) ∧ (v = a.1 ∨ v = a.2.1 ∨ v = k) ∧ u ≠ v ∧ lpReplicaCurrentFoldedEdge G sites d.1 = s(Sum.inl (sites u), Sum.inl (sites v)) ∧ let l := lpReplicaThirdOfThree a.1 a.2.1 k u v l ≠ u ∧ l ≠ v ∧ (l = a.1 ∨ l = a.2.1 ∨ l = k) := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateUnmarkedSaturatedSourceRankFive_exists_labeledRoute G sites hsite q hcard z


-- created on 2026-10-23
