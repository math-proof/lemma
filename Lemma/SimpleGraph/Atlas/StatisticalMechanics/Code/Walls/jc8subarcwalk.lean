import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc8subarcwalk
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc8_loop_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_loop_isCycle_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ jc7_choosePeriod K hK e he)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he))) :
-- imply
  (olb_orbitLoop K hK e he).IsCycle := by
-- proof
  apply StatMech.Walls.jc8_loop_isCycle K hK e he hp hinj

/--
[jc8_substretch_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_start_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert 0 = u := by
-- proof
  apply StatMech.Walls.jc8_substretch_start K hK e he hu hv

/--
[jc8_substretch_finish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_finish_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length = v := by
-- proof
  apply StatMech.Walls.jc8_substretch_finish K hK e he hu hv

/--
[jc8_substretch_adj_getVert_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_adj_getVert_succ_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
  {i : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
  (hi : i < (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length) :
-- imply
  (hypercubicLattice 2).Adj ((((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert i) ((((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert (i + 1)) := by
-- proof
  apply StatMech.Walls.jc8_substretch_adj_getVert_succ K hK e he hu hv hi

/--
[jc8_substretch_isSubwalk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_isSubwalk_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).IsSubwalk (olb_orbitLoop K hK e he) := by
-- proof
  apply StatMech.Walls.jc8_substretch_isSubwalk K hK e he hu hv

/--
[jc8_dropUntil_support_sublist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_dropUntil_support_sublist_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support) :
-- imply
  ((olb_orbitLoop K hK e he).dropUntil u hu).support.Sublist (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Walls.jc8_dropUntil_support_sublist K hK e he hu

/--
[jc8_substretch_support_sublist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_support_sublist_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support.Sublist (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Walls.jc8_substretch_support_sublist K hK e he hu hv

/--
[jc8_substretch_support_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_support_subset_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support ⊆ (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Walls.jc8_substretch_support_subset K hK e he hu hv

/--
[jc8_substretch_darts_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_darts_subset_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).darts ⊆ (olb_orbitLoop K hK e he).darts := by
-- proof
  apply StatMech.Walls.jc8_substretch_darts_subset K hK e he hu hv

/--
[jc8_substretch_edges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_edges_subset_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).edges ⊆ (olb_orbitLoop K hK e he).edges := by
-- proof
  apply StatMech.Walls.jc8_substretch_edges_subset K hK e he hu hv

/--
[jc8_getVert_dropUntil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_getVert_dropUntil_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u : Site 2}
  {k : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support) :
-- imply
  ((olb_orbitLoop K hK e he).dropUntil u hu).getVert k = (olb_orbitLoop K hK e he).getVert ((olb_orbitLoop K hK e he).support.idxOf u + k) := by
-- proof
  apply StatMech.Walls.jc8_getVert_dropUntil K hK e he hu k

/--
[jc8_idxOf_add_le_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_idxOf_add_le_length_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
  {k : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
  (hk : k ≤ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length) :
-- imply
  (olb_orbitLoop K hK e he).support.idxOf u + k ≤ (olb_orbitLoop K hK e he).length := by
-- proof
  apply StatMech.Walls.jc8_idxOf_add_le_length K hK e he hu hv k hk

/--
[jc8_substretch_getVert_eq_dartFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_getVert_eq_dartFace_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
  {k : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
  (hk : k ≤ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert k = dartFace ((dartNext K)^[(olb_orbitLoop K hK e he).support.idxOf u + k] e) := by
-- proof
  apply StatMech.Walls.jc8_substretch_getVert_eq_dartFace K hK e he hu hv k hk

/--
[jc8_substretch_support_eq_map](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_support_eq_map_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support = (List.range ((((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).length + 1)).map (fun k => dartFace ((dartNext K)^[(olb_orbitLoop K hK e he).support.idxOf u + k] e)) := by
-- proof
  apply StatMech.Walls.jc8_substretch_support_eq_map K hK e he hu hv

/--
[jc8_idxOf_eq_takeUntil_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_idxOf_eq_takeUntil_length_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support) :
-- imply
  (olb_orbitLoop K hK e he).support.idxOf u = ((olb_orbitLoop K hK e he).takeUntil u hu).length := by
-- proof
  apply StatMech.Walls.jc8_idxOf_eq_takeUntil_length K hK e he hu

/--
[jc8_substretch_getVert_zero_eq_dartFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8subarcwalk.lean)
-/
@[path]
private lemma jc8_substretch_getVert_zero_eq_dartFace_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support) :
-- imply
  (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).getVert 0 = dartFace ((dartNext K)^[(olb_orbitLoop K hK e he).support.idxOf u] e) := by
-- proof
  apply StatMech.Walls.jc8_substretch_getVert_zero_eq_dartFace K hK e he hu hv


-- created on 2026-10-23
