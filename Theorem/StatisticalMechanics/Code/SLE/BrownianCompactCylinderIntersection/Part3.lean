/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/BrownianCompactCylinderIntersection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.SLE.BrownianProjectiveContent
import Mathlib.Topology.Bornology.Constructions
import Mathlib.Topology.MetricSpace.Bounded
import Def.StatisticalMechanics.Code.SLE.BrownianCompactCylinderIntersection.Part2
open MeasureTheory Set


namespace StatMech.SLE

theorem cylinder_cylinderPrefixBase
    (I : Nat -> Finset Real) (L : forall k, Set (I k -> Real))
    (n : Nat) :
    (cylinder (cylinderPrefixSupport I n) (cylinderPrefixBase I L n) :
        Set (Real -> Real)) =
      iInter (fun k => iInter (fun _hkn : k <= n =>
        (cylinder (I k) (L k) : Set (Real -> Real)))) := by
  ext x
  simp only [mem_cylinder, cylinderPrefixBase, Set.mem_setOf_eq,
    Set.mem_iInter]
  rfl


theorem cylinderPrefixBase_isCompact
    (I : Nat -> Finset Real) (L : forall k, Set (I k -> Real))
    (hcompact : forall k, IsCompact (L k)) (n : Nat) :
    IsCompact (cylinderPrefixBase I L n) := by
  classical
  have hclosed : IsClosed (cylinderPrefixBase I L n) := by
    rw [show cylinderPrefixBase I L n =
      iInter (fun k => iInter (fun hkn : k <= n =>
        Finset.restrict₂
          (π := fun _ : Real => Real)
          (cylinderPrefixSupport_subset I hkn) ⁻¹' L k)) by
      ext x
      simp only [cylinderPrefixBase, Set.mem_setOf_eq, Set.mem_iInter,
        Set.mem_preimage]]
    exact isClosed_iInter fun k => isClosed_iInter fun hkn =>
      (hcompact k).isClosed.preimage
        (Finset.continuous_restrict₂ (cylinderPrefixSupport_subset I hkn))
  have hbounded : Bornology.IsBounded (cylinderPrefixBase I L n) := by
    rw [← Bornology.forall_isBounded_image_eval_iff]
    intro q
    have hq : (q : Real) ∈ cylinderPrefixSupport I n := q.property
    change (q : Real) ∈ (Finset.range (n + 1)).biUnion I at hq
    rw [Finset.mem_biUnion] at hq
    obtain ⟨k, hkRange, hqk⟩ := hq
    have hkn : k <= n := by
      rw [Finset.mem_range] at hkRange
      omega
    apply (hcompact k).isBounded.image_eval ⟨q, hqk⟩ |>.subset
    rintro z ⟨x, hx, rfl⟩
    let y : I k -> Real :=
      Finset.restrict₂
        (π := fun _ : Real => Real)
        (cylinderPrefixSupport_subset I hkn) x
    refine ⟨y, hx k hkn, ?_⟩
    rfl
  exact Metric.isCompact_iff_isClosed_bounded.2 ⟨hclosed, hbounded⟩

end StatMech.SLE
