/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PivotalFactorFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Def.StatisticalMechanics.Code.Sharpness.PivotalFactorFull.Part3
open MeasureTheory Function Set
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem shp_connWithin_transfer {ω ω' : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    (hagree : ∀ e ∈ internalEdges S, ω e = ω' e)
    {a b : ↥S} (h : ConnectedWithin d ω S a b) : ConnectedWithin d ω' S a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v t hadj p ih =>
    have hopen : IsOpenEdge d ω (u : Site d) (v : Site d) := hadj
    obtain ⟨hadj0, hop⟩ := hopen
    have hopen' : IsOpenEdge d ω' (u : Site d) (v : Site d) := by
      refine ⟨hadj0, ?_⟩
      rw [← hagree _ ⟨(u : Site d), u.2, (v : Site d), v.2, rfl⟩]; exact hop
    exact (SimpleGraph.Adj.reachable
      (show (openSubgraphInduce d ω' S).Adj u v from hopen')).trans ih


theorem shp_connWithinEvent_congr {S : Set (Site d)} {o x : Site d}
    {ω ω' : ConfigSpace (Sym2 (Site d))}
    (hagree : ∀ e ∈ internalEdges S, ω e = ω' e) :
    ω ∈ connWithinEvent d S o x ↔ ω' ∈ connWithinEvent d S o x := by
  constructor
  · rintro ⟨ho, hx, hc⟩; exact ⟨ho, hx, shp_connWithin_transfer hagree hc⟩
  · rintro ⟨ho, hx, hc⟩
    exact ⟨ho, hx, shp_connWithin_transfer (fun e he => (hagree e he).symm) hc⟩


theorem shp_connWithinEvent_dependsOn {S : Finset (Site d)} {o x : Site d} :
    DependsOn ((connWithinEvent d (S : Set (Site d)) o x).indicator (fun _ => (1 : ℝ)))
      (internalEdgesFinset S : Set (Sym2 (Site d))) := by
  intro ω ω' h
  rw [internalEdgesFinset_coe] at h
  have hiff := shp_connWithinEvent_congr (S := (S : Set (Site d))) (o := o) (x := x)
    (fun e he => h e he)
  by_cases hω : ω ∈ connWithinEvent d (S : Set (Site d)) o x
  · rw [Set.indicator_of_mem hω, Set.indicator_of_mem (hiff.mp hω)]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_notMem (fun hc => hω (hiff.mpr hc))]


theorem shp_connWithin_factor (p : NNReal) (hp : p ≤ 1)
    (S : Finset (Site d)) (o x : Site d)
    (B : Set (ConfigSpace (Sym2 (Site d)))) (U : Finset (Sym2 (Site d)))
    (hdisj : Disjoint (internalEdgesFinset S) U)
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connWithinEvent d (S : Set (Site d)) o x ∩ B)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connWithinEvent d (S : Set (Site d)) o x)
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B :=
  indep_cylinder_inf p hp _ B (internalEdgesFinset S) U hdisj
    shp_connWithinEvent_dependsOn hB


theorem shp_pivotal_factor (p : NNReal) (hp : p ≤ 1)
    (S : Finset (Site d)) (o x : Site d)
    (B : Set (ConfigSpace (Sym2 (Site d)))) (U : Finset (Sym2 (Site d)))
    (hUext : ∀ e ∈ U, ∃ a b : Site d, e = s(a, b) ∧ (a ∉ (S : Set (Site d)) ∨ b ∉ (S : Set (Site d))))
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connWithinEvent d (S : Set (Site d)) o x ∩ B)
      = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connWithinEvent d (S : Set (Site d)) o x)
        * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B :=
  shp_connWithin_factor p hp S o x B U (shp_internalEdgesFinset_disjoint hUext) hB

end Sharpness
end StatMech
