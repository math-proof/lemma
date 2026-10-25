/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7core.lean -/

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
import Theorem.StatisticalMechanics.Code.Walls.jc5_footprintdartsfinite
import Theorem.StatisticalMechanics.Code.Walls.jc6_ivt.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7ivtnohop
import Theorem.StatisticalMechanics.Code.Walls.jc7getverteqdartface
import Theorem.StatisticalMechanics.Code.Walls.jc7loopiscycle
import Theorem.StatisticalMechanics.Code.Walls.jc7loopseparates.Part2
import Theorem.StatisticalMechanics.Code.Walls.jc7stepfacebridge
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Def.StatisticalMechanics.Code.Walls.jc7core
open SimpleGraph Function Set


namespace StatMech

namespace Walls

open StatMech.Lattice


theorem jc7_singlePass_iff_touchingConvex (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2) :
    jc7_SinglePass K a r ↔ jc5_TouchingConvex K a r :=
  Iff.rfl


theorem jc7_touchingConvex (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hsp : jc7_SinglePass K a r) : jc5_TouchingConvex K a r :=
  hsp


theorem jc7_noReentry_of_singlePass (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (ha0 : ¬ jc4_FootprintFree K a r 0) (hsp : jc7_SinglePass K a r) :
    jc5_NoReentry K a r :=
  jc5_noReentry_of_convex K a r ha0 (jc7_touchingConvex K a r hsp)


theorem jc7_tailFootprintFree_of_singlePass (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0) (hsp : jc7_SinglePass K a r) :
    jc4_TailFootprintFree K a r (jc4_firstReturnK K a r hex)
      (dartOrbitPeriod K a - jc4_firstReturnK K a r hex) :=
  jc5_tailFootprintFree_of_convex K a r hex ha0 (jc7_touchingConvex K a r hsp)


theorem jc7_excursionConfined_of_singlePass (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (r : Site 2)
    (hex : ∃ i, 1 ≤ i ∧ jc4_FootprintFree K a r i)
    (ha0 : ¬ jc4_FootprintFree K a r 0) (hsp : jc7_SinglePass K a r) :
    jc5_ExcursionConfined K a r hex :=
  jc5_excursionConfined_of_convex K a r hex ha0 (jc7_touchingConvex K a r hsp)


theorem jc7core_orbit_isCycle (K : Set (Site 2)) (hK : K.Finite) : jc6_SingleCycle K :=
  jc7_orbit_isCycle K hK


theorem jc7core_getVert_eq_dartFace (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) (n : ℕ) (hn : n ≤ (olb_orbitLoop K hK e he).length) :
    (olb_orbitLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) :=
  jc7_getVert_eq_dartFace K hK e he n hn


theorem jc7core_loop_separates (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2} (hadj : (hypercubicLattice 2).Adj u v)
    (hbd : bdEdge (jec_leftRegion (olb_orbitLoop K hK e he)) s(u, v)) :
    u ∈ (olb_orbitLoop K hK e he).support ∨ v ∈ (olb_orbitLoop K hK e he).support :=
  jc7_loop_leftRegion_bdEdge_support K hK e he hadj hbd


theorem jc7core_subStretch_cannot_hop (K : Set (Site 2)) (hK : K.Finite) (e : Dart)
    (he : IsBoundaryDart K e) {u v : Site 2}
    (hu : u ∈ (olb_orbitLoop K hK e he).support)
    (hv : v ∈ ((olb_orbitLoop K hK e he).dropUntil u hu).support)
    (ρ : ℤ)
    (hmiss : ∀ p ∈ (((olb_orbitLoop K hK e he).dropUntil u hu).takeUntil v hv).support, p 1 ≠ ρ) :
    ρ < min (u 1) (v 1) ∨ max (u 1) (v 1) < ρ :=
  jc7_subStretch_cannot_hop K hK e he hu hv ρ hmiss


theorem jc7_singlePass_of_disjoint (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hfoot : ∀ i, jc4_FootprintFree K a r i) :
    jc7_SinglePass K a r := by
  intro i j k _ _ hi _
  exact absurd (hfoot i) hi


theorem jc7_touchingConvex_of_disjoint (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hfoot : ∀ i, jc4_FootprintFree K a r i) :
    jc5_TouchingConvex K a r :=
  jc7_touchingConvex K a r (jc7_singlePass_of_disjoint K a r hfoot)


theorem jc7_band_vacuous_of_disjoint (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e})
    (r : Site 2) (hfoot : ∀ i, jc4_FootprintFree K a r i) (i : ℕ) :
    jc4_FootprintFree K a r i :=
  hfoot i


end Walls
end StatMech
