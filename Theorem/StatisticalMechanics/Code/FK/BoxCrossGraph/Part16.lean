/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoxCrossGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Instance.StatisticalMechanics.Code.FK.BoxCrossGraph.Part3
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem crossWiredGraphAdd_adj_boxVertIncl (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) (x y : boxVerts d n) :
    (crossWiredGraphAdd d n ω D).Adj (boxVertIncl d n x) (boxVertIncl d n y)
      ↔ (innerWiredGraph d n ω).Adj x y := by
  rw [crossWiredGraphAdd, SimpleGraph.sup_adj]
  constructor
  · rintro (hcross | hd)
    · exact (crossWiredGraph_adj_boxVertIncl d n ω x y).mp hcross
    · exact absurd (isInnerVert_boxVertIncl d n x) (hD hd)
  · intro h
    exact Or.inl ((crossWiredGraph_adj_boxVertIncl d n ω x y).mpr h)


theorem crossWiredGraphAdd_adj_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (D : SimpleGraph (boxVerts d (n+1)))
    (a b : AnnulusVert d n) :
    (crossWiredGraphAdd d n ω D).Adj a.1 b.1 ↔ (annulusSubgraph d n D).Adj a b := by
  rw [crossWiredGraphAdd, SimpleGraph.sup_adj, annulusSubgraph, SimpleGraph.comap_adj]
  constructor
  · rintro (hcross | hd)
    · exact absurd hcross (crossWiredGraph_not_adj_of_annulus d n ω a.2 b.1)
    · exact hd
  · intro h; exact Or.inr h


theorem inner_reachable_of_crossWiredGraphAdd (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {x y : boxVerts d n}
    (h : (crossWiredGraphAdd d n ω D).Reachable (boxVertIncl d n x) (boxVertIncl d n y)) :
    (innerWiredGraph d n ω).Reachable x y := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen (crossWiredGraphAdd d n ω D).Adj (boxVertIncl d n x) w →
        ∀ (hw : IsInnerVert d n w),
          (innerWiredGraph d n ω).Reachable x ⟨(w : Site d), hw⟩ by
    have := H (boxVertIncl d n y) h (isInnerVert_boxVertIncl d n y)
    convert this using 2
  intro w hw hwinner
  induction hw with
  | refl =>
      have : (⟨(boxVertIncl d n x : Site d), hwinner⟩ : boxVerts d n) = x := by
        apply Subtype.ext; rfl
      rw [this]
  | @tail u w hux hadj ih =>
      have huinner : IsInnerVert d n u :=
        crossWiredGraphAdd_reachable_inner d n ω hD (isInnerVert_boxVertIncl d n x)
          (SimpleGraph.reachable_iff_reflTransGen .. |>.mpr hux)
      have ihu := ih huinner
      have hue : u = boxVertIncl d n ⟨(u : Site d), huinner⟩ := by apply Subtype.ext; rfl
      have hwe : w = boxVertIncl d n ⟨(w : Site d), hwinner⟩ := by apply Subtype.ext; rfl
      have hadj' : (crossWiredGraphAdd d n ω D).Adj
          (boxVertIncl d n ⟨(u : Site d), huinner⟩)
          (boxVertIncl d n ⟨(w : Site d), hwinner⟩) := by rw [← hue, ← hwe]; exact hadj
      have hstep := (crossWiredGraphAdd_adj_boxVertIncl d n ω hD
        ⟨(u : Site d), huinner⟩ ⟨(w : Site d), hwinner⟩).mp hadj'
      exact ihu.trans hstep.reachable


theorem annulus_reachable_of_crossWiredGraphAdd (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {a b : AnnulusVert d n}
    (h : (crossWiredGraphAdd d n ω D).Reachable a.1 b.1) :
    (annulusSubgraph d n D).Reachable a b := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  suffices H : ∀ w : boxVerts d (n+1),
      Relation.ReflTransGen (crossWiredGraphAdd d n ω D).Adj a.1 w →
        ∀ (hw : ¬ IsInnerVert d n w),
          (annulusSubgraph d n D).Reachable a ⟨w, hw⟩ by
    have hb := H b.1 h b.2
    have : (⟨b.1, b.2⟩ : AnnulusVert d n) = b := Subtype.ext rfl
    rwa [this] at hb
  intro w hw hwannulus
  induction hw with
  | refl =>
      have : (⟨a.1, hwannulus⟩ : AnnulusVert d n) = a := Subtype.ext rfl
      rw [this]
  | @tail u w hau hadj ih =>
      have huannulus : ¬ IsInnerVert d n u :=
        crossWiredGraphAdd_reachable_annulus d n ω hD a.2
          (SimpleGraph.reachable_iff_reflTransGen .. |>.mpr hau)
      have ihu := ih huannulus
      have hstep := (crossWiredGraphAdd_adj_annulus d n ω D
        ⟨u, huannulus⟩ ⟨w, hwannulus⟩).mp hadj
      exact ihu.trans hstep.reachable


end FK
end StatMech
