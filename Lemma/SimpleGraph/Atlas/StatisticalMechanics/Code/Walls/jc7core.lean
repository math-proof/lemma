import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc7core.Part2
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc7_head_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_head_eq_eq
  {e : Dart} :
-- imply
  e.head = e.tail + e.dir := by
-- proof
  apply StatMech.Walls.jc7_head_eq e

/--
[jc7_face_row_le_one_of_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_face_row_le_one_of_tail_eq
  {e : Dart} :
-- imply
  (dartFace e 1 - e.tail 1).natAbs ≤ 1 := by
-- proof
  apply StatMech.Walls.jc7_face_row_le_one_of_tail e

/--
[jc7_face_row_dist_tailTravel_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_face_row_dist_tailTravel_le_two_eq
  {e : Dart} :
-- imply
  (dartFace e 1 - jc_tailTravel e 1).natAbs ≤ 2 := by
-- proof
  apply StatMech.Walls.jc7_face_row_dist_tailTravel_le_two e

/--
[jc7_face_row_dist_headTravel_le_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_face_row_dist_headTravel_le_two_eq
  {e : Dart} :
-- imply
  (dartFace e 1 - jc_headTravel e 1).natAbs ≤ 2 := by
-- proof
  apply StatMech.Walls.jc7_face_row_dist_headTravel_le_two e

/--
[jc7_footprint_row_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_footprint_row_le_one_eq
  {r x : Site 2}
-- given
  (hx : x ∈ jc3_earFootprint r) :
-- imply
  (x 1 - r 1).natAbs ≤ 1 := by
-- proof
  apply StatMech.Walls.jc7_footprint_row_le_one r x hx

/--
[jc7_touching_face_row_band](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_touching_face_row_band_eq
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc5_ProbesEarFootprint r e) :
-- imply
  (dartFace e 1 - r 1).natAbs ≤ 3 := by
-- proof
  apply StatMech.Walls.jc7_touching_face_row_band r e h

/--
[jc7_touching_face_row_band'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_touching_face_row_band'_eq
  {r : Site 2}
  {e : Dart}
-- given
  (h : jc5_ProbesEarFootprint r e) :
-- imply
  r 1 - 3 ≤ dartFace e 1 ∧ dartFace e 1 ≤ r 1 + 3 := by
-- proof
  apply StatMech.Walls.jc7_touching_face_row_band' r e h

/--
[jc7_touching_iff_probes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_touching_iff_probes_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {i : ℕ} :
-- imply
  ¬ jc4_FootprintFree K a r i ↔ jc5_ProbesEarFootprint r ((dartNext K)^[i] a.1) := by
-- proof
  apply StatMech.Walls.jc7_touching_iff_probes K a r i

/--
[jc7_touching_orbitFace_row_band](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_touching_orbitFace_row_band_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {i : ℕ}
-- given
  (h : ¬ jc4_FootprintFree K a r i) :
-- imply
  (dartFace ((dartNext K)^[i] a.1) 1 - r 1).natAbs ≤ 3 := by
-- proof
  apply StatMech.Walls.jc7_touching_orbitFace_row_band K a r i h

/--
[jc7_touching_loopVert_row_band](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_touching_loopVert_row_band_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {i : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hi : i ≤ (olb_orbitLoop K hK e he).length)
  (h : ¬ jc4_FootprintFree K ⟨e, he⟩ r i) :
-- imply
  ((olb_orbitLoop K hK e he).getVert i 1 - r 1).natAbs ≤ 3 := by
-- proof
  apply StatMech.Walls.jc7_touching_loopVert_row_band K hK e he r i hi h

/--
[jc7_singlePass_iff_touchingConvex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_singlePass_iff_touchingConvex_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2} :
-- imply
  jc7_SinglePass K a r ↔ jc5_TouchingConvex K a r := by
-- proof
  apply StatMech.Walls.jc7_singlePass_iff_touchingConvex K a r

/--
[jc7_touchingConvex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_touchingConvex_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hsp : jc7_SinglePass K a r) :
-- imply
  jc5_TouchingConvex K a r := by
-- proof
  apply StatMech.Walls.jc7_touchingConvex K a r hsp

/--
[jc7_noReentry_of_singlePass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_noReentry_of_singlePass_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (ha0 : ¬ jc4_FootprintFree K a r 0)
  (hsp : jc7_SinglePass K a r) :
-- imply
  jc5_NoReentry K a r := by
-- proof
  apply StatMech.Walls.jc7_noReentry_of_singlePass K a r ha0 hsp

/--
[jc7_tailFootprintFree_of_singlePass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_tailFootprintFree_of_singlePass_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (ha0 : ¬ jc4_FootprintFree K a r 0)
  (hsp : jc7_SinglePass K a r) :
-- imply
  jc4_TailFootprintFree K a r (jc4_firstReturnK K a r hex) (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) := by
-- proof
  apply StatMech.Walls.jc7_tailFootprintFree_of_singlePass K a r hex ha0 hsp

/--
[jc7_excursionConfined_of_singlePass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_excursionConfined_of_singlePass_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
  (ha0 : ¬ jc4_FootprintFree K a r 0)
  (hsp : jc7_SinglePass K a r) :
-- imply
  jc5_ExcursionConfined K a r hex := by
-- proof
  apply StatMech.Walls.jc7_excursionConfined_of_singlePass K a r hex ha0 hsp

/--
[jc7core_orbit_isCycle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7core_orbit_isCycle_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite) :
-- imply
  jc6_SingleCycle K := by
-- proof
  apply StatMech.Walls.jc7core_orbit_isCycle K hK

/--
[jc7core_getVert_eq_dartFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7core_getVert_eq_dartFace_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hn : n ≤ (olb_orbitLoop K hK e he).length) :
-- imply
  (olb_orbitLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) := by
-- proof
  apply StatMech.Walls.jc7core_getVert_eq_dartFace K hK e he n hn

/--
[jc7core_loop_separates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7core_loop_separates_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hadj : (hypercubicLattice 2).Adj u v)
  (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
-- imply
  u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support := by
-- proof
  apply StatMech.Walls.jc7core_loop_separates K hK e he hadj hbd

/--
[jc7core_subStretch_cannot_hop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7core_subStretch_cannot_hop_eq
  {K : Set (Site 2)}
  {e : Dart}
  {u v : Site 2}
  {ρ : ℤ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hu : u ∈ (olb_orbitLoop K hK e he).support)
  (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
  (hmiss : ∀ p ∈ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support, p 1 ≠ ρ) :
-- imply
  ρ < min (u 1) (v 1) ∨ max (u 1) (v 1) < ρ := by
-- proof
  apply StatMech.Walls.jc7core_subStretch_cannot_hop K hK e he hu hv ρ hmiss

/--
[jc7_singlePass_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_singlePass_of_disjoint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, jc4_FootprintFree K a r i) :
-- imply
  jc7_SinglePass K a r := by
-- proof
  apply StatMech.Walls.jc7_singlePass_of_disjoint K a r hfoot

/--
[jc7_touchingConvex_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_touchingConvex_of_disjoint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
-- given
  (hfoot : ∀ i, jc4_FootprintFree K a r i) :
-- imply
  jc5_TouchingConvex K a r := by
-- proof
  apply StatMech.Walls.jc7_touchingConvex_of_disjoint K a r hfoot

/--
[jc7_band_vacuous_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean)
-/
@[path]
private lemma jc7_band_vacuous_of_disjoint_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {r : Site 2}
  {i : ℕ}
-- given
  (hfoot : ∀ i, jc4_FootprintFree K a r i) :
-- imply
  jc4_FootprintFree K a r i := by
-- proof
  apply StatMech.Walls.jc7_band_vacuous_of_disjoint K a r hfoot i


-- created on 2026-10-23
