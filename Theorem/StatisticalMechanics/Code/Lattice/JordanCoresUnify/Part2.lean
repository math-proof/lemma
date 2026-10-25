/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanCoresUnify.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.ArcSides.Part3
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.InterfaceConnected.Part8
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Def.StatisticalMechanics.Code.Lattice.JordanCoresUnify
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.RSW.Box

open StatMech.Universality


theorem jcu_separatingSide_forces_cross {D B inside outside : Set (Site 2)}
    (h : jcu_HasSeparatingSide D B inside outside)
    {x y : Site 2} (hx : x ∈ inside) (hy : y ∈ outside)
    (w : (hypercubicLattice 2).Walk x y) (hwD : ∀ z ∈ w.support, z ∈ D) :
    ∃ z ∈ w.support, z ∈ B := by
  obtain ⟨S, hin, hout, hbd⟩ := h
  have hxS : x ∈ S := hin x hx
  have hyS : y ∉ S := hout y hy
  obtain ⟨u, v, hu, hv, hadj, huS, hvS⟩ := jcu_walk_meets_innerBoundary S hxS hyS w
  rcases hbd u v (hwD u hu) (hwD v hv) hadj huS hvS with hB | hB
  · exact ⟨u, hu, hB⟩
  · exact ⟨v, hv, hB⟩


theorem jcu_floodFill_separatingSide (ω : ConfigSpace (Sym2 (Site 2)))
    (α β m m' c d : ℤ) (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    {x y : Site 2} (hx : x ∈ rect α β c d) (hxα : x 0 = α)
    (hii : y ∉ arcS_leftRegion ω α β m m' c d xB hxB) :
    jcu_HasSeparatingSide (rect α β c d) (overlapComp ω m m' c d xB hxB) {x} {y} := by
  refine ⟨arcS_leftRegion ω α β m m' c d xB hxB, ?_, ?_, ?_⟩
  · 
    intro z hz
    rw [Set.mem_singleton_iff] at hz; subst z
    exact arcS_leftRegion_left ω α β m m' c d xB hxB x hx hxα
  · 
    intro z hz
    rw [Set.mem_singleton_iff] at hz; subst z; exact hii
  · 
    intro u v huD hvD hadj huS hvS
    apply arcS_leftRegion_bdEdge ω α β m m' c d xB hxB u v huD hvD hadj
    rw [bdEdge_mk]; exact ⟨fun _ => hvS, fun _ => huS⟩


theorem jcu_discreteJordan_imp_twoPathsCross (ω : ConfigSpace (Sym2 (Site 2)))
    (α β m m' c d : ℤ) (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    (hii : ∀ y : Site 2, y ∈ rect α β c d → y 0 = β →
      y ∉ arcS_leftRegion ω α β m m' c d xB hxB) :
    ArcS_TwoPathsCross ω α β m m' c d xB hxB := by
  intro _hαm _hmm' _hm'β x y hx hy hxα hyβ γ hsupp
  obtain ⟨z, hz, hzP⟩ :=
    jcu_separatingSide_forces_cross
      (jcu_floodFill_separatingSide ω α β m m' c d xB hxB hx hxα (hii y hy hyβ))
      rfl rfl γ hsupp
  exact ⟨z, hz, hzP⟩


theorem jcu_interface_separation (K : Set (Site 2)) {x y : Site 2}
    (hx : x ∈ K) (hy : y ∉ K) (w : (hypercubicLattice 2).Walk x y) :
    ∃ e ∈ w.edges, bdEdge K e :=
  jcu_walk_crosses K hx hy w


theorem jcu_discreteJordan_imp_interfaceConnected (K : Set (Site 2))
    (htr : OrbitKingTransport K) (hcon : BoundaryKingConnected K)
    (hsat : OrbitVertexSaturate K) :
    InterfaceConnected K :=
  interfaceConnected_of_kingResidues K htr hcon hsat


theorem jcu_discreteJordan_imp_orbitFaceNoPinch (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e})
    (hsimple : ∀ i ∈ Set.Iio (dartOrbitPeriod K a), ∀ j ∈ Set.Iio (dartOrbitPeriod K a),
      dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1) →
        (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1) :
    OrbitFaceNoPinch K a := by
  intro i hi j hj hface
  
  rw [hsimple i hi j hj hface]


theorem jcu_orbitFaceNoPinch_imp_simple (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : OrbitFaceNoPinch K a)
    {i j : ℕ} (hi : i ∈ Set.Iio (dartOrbitPeriod K a)) (hj : j ∈ Set.Iio (dartOrbitPeriod K a))
    (hface : dartFace ((dartNext K)^[i] a.1) = dartFace ((dartNext K)^[j] a.1)) :
    (dartNext K)^[i] a.1 = (dartNext K)^[j] a.1 :=
  dartFace_eq_of_dir_eq (h i hi j hj hface) hface


theorem jcu_orbitFaceNoPinch_imp_injOn (K : Set (Site 2))
    (a : {e : Dart // IsBoundaryDart K e}) (h : OrbitFaceNoPinch K a) :
    Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a)) :=
  orbitFace_injOn_of_noPinch K a h


theorem jcu_twoPathsCross_of_floodFill_ii (ω : ConfigSpace (Sym2 (Site 2)))
    (α β m m' c d : ℤ) (xB : Site 2) (hxB : xB ∈ rect m m' c d)
    (hii : ∀ y : Site 2, y ∈ rect α β c d → y 0 = β →
      y ∉ arcS_leftRegion ω α β m m' c d xB hxB) :
    ArcS_TwoPathsCross ω α β m m' c d xB hxB :=
  jcu_discreteJordan_imp_twoPathsCross ω α β m m' c d xB hxB hii

end Lattice
end StatMech
