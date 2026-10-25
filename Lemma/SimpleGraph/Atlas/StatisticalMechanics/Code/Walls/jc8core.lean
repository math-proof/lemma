import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc8core.Part4
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc8c_touchingFace_ne_descentFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_touchingFace_ne_descentFace_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {j : ℕ}
  {u : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hj : j ≤ (olb_orbitLoop K hK e he).length)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j)
  (hu : u 1 ≤ r 1 - 4) :
-- imply
  u 1 < (olb_orbitLoop K hK e he).getVert j 1 ∧ u ≠ (olb_orbitLoop K hK e he).getVert j := by
-- proof
  apply StatMech.Walls.jc8c_touchingFace_ne_descentFace K hK e he r j hj htouch u hu

/--
[jc8c_distinct_touch_descent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_distinct_touch_descent_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {i j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hi : i ≤ (olb_orbitLoop K hK e he).length)
  (hti : ¬ jc4_FootprintFree K ⟨e, he⟩ r i)
  (hdesc : (olb_orbitLoop K hK e he).getVert j 1 ≤ r 1 - 4) :
-- imply
  (olb_orbitLoop K hK e he).getVert i ≠ (olb_orbitLoop K hK e he).getVert j := by
-- proof
  apply StatMech.Walls.jc8c_distinct_touch_descent K hK e he r i j hi hti hdesc

/--
[jc8c_crossCount_ge_one_touch_to_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_crossCount_ge_one_touch_to_free_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {j₀ j₁ : ℕ}
  {w : (hypercubicLattice 2).Walk ((olb_orbitLoop K hK e he).getVert j₀) ((olb_orbitLoop K hK e he).getVert j₁)}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hdich : jc8c_SideDichotomy K hK e he r)
  (hj₀ : j₀ ≤ (olb_orbitLoop K hK e he).length)
  (hj₁ : j₁ ≤ (olb_orbitLoop K hK e he).length)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j₀)
  (hfree : jc4_FootprintFree K ⟨e, he⟩ r j₁) :
-- imply
  1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w := by
-- proof
  apply StatMech.Walls.jc8c_crossCount_ge_one_touch_to_free K hK e he r hdich hj₀ hj₁ htouch hfree w

/--
[jc8c_touchingConvex_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_touchingConvex_window_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {i j k : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hdich : jc8c_SideDichotomy K hK e he r)
  (hint : jc8c_InsideInterval K hK e he)
  (hi : i ≤ (olb_orbitLoop K hK e he).length)
  (hj : j ≤ (olb_orbitLoop K hK e he).length)
  (hk : k ≤ (olb_orbitLoop K hK e he).length)
  (hij : i < j)
  (hjk : j < k)
  (hti : ¬ jc4_FootprintFree K ⟨e, he⟩ r i)
  (htk : ¬ jc4_FootprintFree K ⟨e, he⟩ r k) :
-- imply
  ¬ jc4_FootprintFree K ⟨e, he⟩ r j := by
-- proof
  apply StatMech.Walls.jc8c_touchingConvex_window K hK e he r hdich hint i j k hi hj hk hij hjk hti htk

/--
[jc8c_touchingConvex_of_residue_windowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_touchingConvex_of_residue_windowed_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hres : jc8c_InsideIntervalResidue K hK e he r) :
-- imply
  ∀ i j k, i ≤ (olb_orbitLoop K hK e he).length → j ≤ (olb_orbitLoop K hK e he).length → k ≤ (olb_orbitLoop K hK e he).length → i < j → j < k → ¬ jc4_FootprintFree K ⟨e, he⟩ r i → ¬ jc4_FootprintFree K ⟨e, he⟩ r k → ¬ jc4_FootprintFree K ⟨e, he⟩ r j := by
-- proof
  apply StatMech.Walls.jc8c_touchingConvex_of_residue_windowed K hK e he r hres

/--
[jc8c_touchingConvex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_touchingConvex_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hres : jc8c_FaceResidue K hK e he r) :
-- imply
  jc5_TouchingConvex K ⟨e, he⟩ r := by
-- proof
  apply StatMech.Walls.jc8c_touchingConvex K hK e he r hres

/--
[jc8c_excursionConfined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_excursionConfined_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K ⟨e, he⟩ r i)
  (ha0 : ¬ jc4_FootprintFree K ⟨e, he⟩ r 0)
  (hres : jc8c_FaceResidue K hK e he r) :
-- imply
  jc5_ExcursionConfined K ⟨e, he⟩ r hex := by
-- proof
  apply StatMech.Walls.jc8c_excursionConfined K hK e he r hex ha0 hres

/--
[jc8c_windowedConvex_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_windowedConvex_of_disjoint_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hfoot : ∀ i, jc4_FootprintFree K ⟨e, he⟩ r i) :
-- imply
  ∀ i j k, i ≤ (olb_orbitLoop K hK e he).length → j ≤ (olb_orbitLoop K hK e he).length → k ≤ (olb_orbitLoop K hK e he).length → i < j → j < k → ¬ jc4_FootprintFree K ⟨e, he⟩ r i → ¬ jc4_FootprintFree K ⟨e, he⟩ r k → ¬ jc4_FootprintFree K ⟨e, he⟩ r j := by
-- proof
  apply StatMech.Walls.jc8c_windowedConvex_of_disjoint K hK e he r hfoot

/--
[jc8c_faceResidue_of_disjoint_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_faceResidue_of_disjoint_empty_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hfoot : ∀ i, jc4_FootprintFree K ⟨e, he⟩ r i)
  (hempty : ∀ i, dartFace ((dartNext K)^[i] e) ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
-- imply
  jc8c_FaceResidue K hK e he r := by
-- proof
  apply StatMech.Walls.jc8c_faceResidue_of_disjoint_empty K hK e he r hfoot hempty

/--
[jc8c_touchingConvex_of_disjoint_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_touchingConvex_of_disjoint_empty_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hfoot : ∀ i, jc4_FootprintFree K ⟨e, he⟩ r i)
  (hempty : ∀ i, dartFace ((dartNext K)^[i] e) ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
-- imply
  jc5_TouchingConvex K ⟨e, he⟩ r := by
-- proof
  apply StatMech.Walls.jc8c_touchingConvex_of_disjoint_empty K hK e he r hfoot hempty

/--
[jc8c_contour_face_count_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_contour_face_count_eq_one_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hp : 3 ≤ jc7_choosePeriod K hK e he)
  (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio (jc7_choosePeriod K hK e he)))
  (hn0 : 0 < n)
  (hnp : n < jc7_choosePeriod K hK e he) :
-- imply
  (olb_orbitLoop K hK e he).support.count (dartFace ((dartNext K)^[n] e)) = 1 := by
-- proof
  apply StatMech.Walls.jc8c_contour_face_count_eq_one K hK e he hp hinj hn0 hnp

/--
[jc8c_bdEdge_lands_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_bdEdge_lands_support_eq
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
  apply StatMech.Walls.jc8c_bdEdge_lands_support K hK e he hadj hbd

/--
[jc8c_crossCount_ge_one_of_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_crossCount_ge_one_of_opposite_eq
  {K : Set (Site 2)}
  {e : Dart}
  {x y : Site 2}
  {w : (hypercubicLattice 2).Walk x y}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hx : x ∈ jec_leftRegion (olb_orbitLoop K hK e he))
  (hy : y ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
-- imply
  1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w := by
-- proof
  apply StatMech.Walls.jc8c_crossCount_ge_one_of_opposite K hK e he w hx hy

/--
[jc8c_bands_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_bands_disjoint_eq
  {r : Site 2} :
-- imply
  Disjoint (jc8_descentBand r) (jc8_touchingBand r) := by
-- proof
  apply StatMech.Walls.jc8c_bands_disjoint r

/--
[jc8c_subStretch_cannot_hop](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_subStretch_cannot_hop_eq
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
  apply StatMech.Walls.jc8c_subStretch_cannot_hop K hK e he hu hv ρ hmiss

/--
[jc8c_touchingFace_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean)
-/
@[path]
private lemma jc8c_touchingFace_lower_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hj : j ≤ (olb_orbitLoop K hK e he).length)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  r 1 - 3 ≤ (olb_orbitLoop K hK e he).getVert j 1 := by
-- proof
  apply StatMech.Walls.jc8c_touchingFace_lower K hK e he r j hj htouch


-- created on 2026-10-23
