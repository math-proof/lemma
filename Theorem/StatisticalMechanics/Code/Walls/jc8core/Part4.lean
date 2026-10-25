/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.jc4_firstreturnK.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc4_tailnotprobed
import Theorem.StatisticalMechanics.Code.Walls.jc5_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7core.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
import Theorem.StatisticalMechanics.Code.Walls.jc8touchingfaceband
import Theorem.StatisticalMechanics.Code.Walls.jc8tworowbands.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc8crossparityleftregion.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc8bdedgelandssupport.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc8cyclenodup
import Theorem.StatisticalMechanics.Code.Walls.jc8subarcwalk
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.OrbitLoopBridge
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Def.StatisticalMechanics.Code.Walls.jc8core.Part3
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc8c_touchingConvex (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hres : jc8c_FaceResidue K hK e he r) :
    jc5_TouchingConvex K ⟨e, he⟩ r := by
  obtain ⟨⟨hTI, hFO⟩, hint⟩ := hres
  intro i j k hij hjk hti htk
  
  have hInsideI := hTI i hti
  have hInsideK := hTI k htk
  
  have hInsideJ := hint i j k hij hjk hInsideI hInsideK
  
  intro hfree
  exact hFO j hfree hInsideJ


theorem jc8c_excursionConfined (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K ⟨e, he⟩ r i)
    (ha0 : ¬ jc4_FootprintFree K ⟨e, he⟩ r 0)
    (hres : jc8c_FaceResidue K hK e he r) :
    jc5_ExcursionConfined K ⟨e, he⟩ r hex :=
  jc5_excursionConfined_of_convex K ⟨e, he⟩ r hex ha0 (jc8c_touchingConvex K hK e he r hres)


theorem jc8c_windowedConvex_of_disjoint (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K ⟨e, he⟩ r i) :
    ∀ i j k, i ≤ (olb_orbitLoop K hK e he).length → j ≤ (olb_orbitLoop K hK e he).length →
      k ≤ (olb_orbitLoop K hK e he).length → i < j → j < k →
      ¬ jc4_FootprintFree K ⟨e, he⟩ r i → ¬ jc4_FootprintFree K ⟨e, he⟩ r k →
      ¬ jc4_FootprintFree K ⟨e, he⟩ r j :=
  fun i _ _ _ _ _ _ _ hti _ => absurd (hfoot i) hti


theorem jc8c_faceResidue_of_disjoint_empty (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K ⟨e, he⟩ r i)
    (hempty : ∀ i, dartFace ((dartNext K)^[i] e) ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
    jc8c_FaceResidue K hK e he r :=
  ⟨⟨fun i hti => absurd (hfoot i) hti, fun i _ => hempty i⟩,
    fun i _ _ _ _ hI _ => absurd hI (hempty i)⟩


theorem jc8c_touchingConvex_of_disjoint_empty (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2)
    (hfoot : ∀ i, jc4_FootprintFree K ⟨e, he⟩ r i)
    (hempty : ∀ i, dartFace ((dartNext K)^[i] e) ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
    jc5_TouchingConvex K ⟨e, he⟩ r :=
  jc8c_touchingConvex K hK e he r (jc8c_faceResidue_of_disjoint_empty K hK e he r hfoot hempty)


theorem jc8c_contour_face_count_eq_one (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e)
    (hp : 3 ≤ jc7_choosePeriod K hK e he)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e))
      (Set.Iio (jc7_choosePeriod K hK e he)))
    {n : ℕ} (hn0 : 0 < n) (hnp : n < jc7_choosePeriod K hK e he) :
    (olb_orbitLoop K hK e he).support.count (dartFace ((dartNext K)^[n] e)) = 1 :=
  jc8_contour_face_count_eq_one K hK e he hp hinj hn0 hnp


theorem jc8c_bdEdge_lands_support (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support :=
  jc8_bdEdge_lands_support K hK e he hadj hbd


theorem jc8c_crossCount_ge_one_of_opposite (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {x y : Site 2}
    (w : (hypercubicLattice 2).Walk x y)
    (hx : x ∈ jec_leftRegion (olb_orbitLoop K hK e he))
    (hy : y ∉ jec_leftRegion (olb_orbitLoop K hK e he)) :
    1 ≤ crossCount (jec_leftRegion (olb_orbitLoop K hK e he)) w :=
  jc8_crossCount_ge_one_of_opposite_leftRegion K hK e he w hx hy


theorem jc8c_bands_disjoint (r : Site 2) :
    Disjoint (jc8_descentBand r) (jc8_touchingBand r) :=
  jc8_bands_disjoint r


theorem jc8c_subStretch_cannot_hop (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (ρ : ℤ)
    (hmiss : ∀ p ∈ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support, p 1 ≠ ρ) :
    ρ < min (u 1) (v 1) ∨ max (u 1) (v 1) < ρ :=
  jc7_subStretch_cannot_hop K hK e he hu hv ρ hmiss


theorem jc8c_touchingFace_lower (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (r : Site 2) (j : ℕ)
    (hj : j ≤ (olb_orbitLoop K hK e he).length)
    (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
    r 1 - 3 ≤ (olb_orbitLoop K hK e he).getVert j 1 :=
  jc8tf_touchingFace_lower K hK e he r j hj htouch


end Walls
end StatMech
