/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Def.StatisticalMechanics.Code.Sharpness.FiniteRangePerco.Part7
open MeasureTheory
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace Lattice Percolation


variable {d : ℕ}


theorem frp_mem_internalEdges {S : Finset (Site d)} {x y : Site d}
    (hx : x ∈ S) (hy : y ∈ S) : s(x, y) ∈ frpInternalEdges S :=
  Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩


theorem frp_connWithin_transfer (K : FiniteRangeKernel d)
    {omega omega' : ConfigSpace (Sym2 (Site d))} {S : Finset (Site d)}
    (hagree : ∀ e ∈ frpInternalEdges S, omega e = omega' e)
    {a b : (S : Set (Site d))}
    (h : ConnWithin (frpGraph K) omega (S : Set (Site d)) a b) :
    ConnWithin (frpGraph K) omega' (S : Set (Site d)) a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v t hadj path ih =>
      have hopen' : (openSub (frpGraph K) omega').Adj (u : Site d) (v : Site d) := by
        refine ⟨hadj.1, ?_⟩
        rw [← hagree s((u : Site d), (v : Site d))
          (frp_mem_internalEdges u.2 v.2)]
        exact hadj.2
      exact (show ((openSub (frpGraph K) omega').induce
        (S : Set (Site d))).Adj u v from hopen').reachable.trans ih


theorem frp_connEvent_dependsOn (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u x : Site d) :
    DependsOn (connEvent (frpGraph K) (S : Set (Site d)) u {x})
      (frpInternalEdges S : Set (Sym2 (Site d))) := by
  intro omega omega' hagree
  constructor
  · rintro ⟨hu, z, hzS, hzx, hconn⟩
    simp only [Set.mem_singleton_iff] at hzx
    subst z
    exact ⟨hu, x, hzS, rfl,
      frp_connWithin_transfer K
        (fun e he => (hagree e (by exact_mod_cast he)).symm) hconn⟩
  · rintro ⟨hu, z, hzS, hzx, hconn⟩
    simp only [Set.mem_singleton_iff] at hzx
    subst z
    exact ⟨hu, x, hzS, rfl,
      frp_connWithin_transfer K
        (fun e he => hagree e (by exact_mod_cast he)) hconn⟩


theorem frp_connEvent_set_dependsOn (K : FiniteRangeKernel d)
    (S : Finset (Site d)) (u : Site d) (B : Set (Site d)) :
    DependsOn (connEvent (frpGraph K) (S : Set (Site d)) u B)
      (frpInternalEdges S : Set (Sym2 (Site d))) := by
  intro omega omega' hagree
  constructor
  · rintro ⟨hu, z, hzS, hzB, hconn⟩
    exact ⟨hu, z, hzS, hzB,
      frp_connWithin_transfer K
        (fun e he => (hagree e (by exact_mod_cast he)).symm) hconn⟩
  · rintro ⟨hu, z, hzS, hzB, hconn⟩
    exact ⟨hu, z, hzS, hzB,
      frp_connWithin_transfer K
        (fun e he => hagree e (by exact_mod_cast he)) hconn⟩


theorem frp_firstExit_inclusion (K : FiniteRangeKernel d)
    (A : Set (Site d)) (S : Finset (Site d)) (B : Set (Site d))
    (u : Site d) (huS : u ∈ S) (hBS : ∀ z ∈ B, z ∉ S) :
    connEvent (frpGraph K) A u B ⊆
      ⋃ q ∈ frpBoundaryPairs K S,
        disjointOccurrence
          (connEvent (frpGraph K) (S : Set (Site d)) u {q.1})
          (disjointOccurrence (edgeOpenEvent q.1 q.2)
            (connEvent (frpGraph K) A q.2 B)) := by
  intro omega homega
  simp only [connEvent, Set.mem_setOf_eq] at homega
  obtain ⟨b, hbA, hbB, path, hsupp⟩ :=
    shk_walk_of_connToSet (frpGraph K) omega A u B homega
  have hbypass_supp : ∀ z ∈ path.bypass.support, z ∈ A := fun z hz =>
    hsupp z (path.support_bypass_subset hz)
  have hbS : b ∉ (S : Set (Site d)) := hBS b hbB
  obtain ⟨x, y, hxS, hyS, hadj, htriple⟩ :=
    shk_firstExit_triple (frpGraph K) omega A (S : Set (Site d)) B
      u b huS hbB hbS path.bypass path.bypass_isPath hbypass_supp
  rw [Set.mem_iUnion₂]
  exact ⟨(x, y), (mem_frpBoundaryPairs K S).mpr ⟨hxS, hyS, hadj⟩, htriple⟩

theorem frp_edgeOpen_dependsOn (x y : Site d) :
    DependsOn (edgeOpenEvent x y)
      ({s(x, y)} : Set (Sym2 (Site d))) := by
  intro omega omega' hagree
  change (omega s(x, y) = true) ↔ (omega' s(x, y) = true)
  rw [hagree s(x, y) (by simp)]


end Sharpness
end StatMech
