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
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part15
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem openSub_sup_eq_crossWiredGraphAdd (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n)))
    (D : SimpleGraph (boxVerts d (n+1))) :
    openSub (boxGraph d (n+1)) (crossExt d n ω)
        ⊔ (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D)
      = crossWiredGraphAdd d n ω D := by
  rw [crossWiredGraphAdd, crossWiredGraph, StatMech.Lattice.wiredGraph,
    StatMech.FK.openSub_eq_openGraph, ← sup_assoc]


theorem crossWiredGraphAdd_adj_inner_right (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (h : (crossWiredGraphAdd d n ω D).Adj u w) :
    IsInnerVert d n w := by
  rw [crossWiredGraphAdd, SimpleGraph.sup_adj] at h
  rcases h with hcross | hd
  · exact crossWiredGraph_adj_inner_right d n ω hu hcross
  · exact absurd hu (hD hd)


theorem crossWiredGraphAdd_not_adj_inner_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (hw : ¬ IsInnerVert d n w) :
    ¬ (crossWiredGraphAdd d n ω D).Adj u w :=
  fun h => hw (crossWiredGraphAdd_adj_inner_right d n ω hD hu h)


theorem crossWiredGraphAdd_reachable_inner (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {u w : boxVerts d (n+1)}
    (hu : IsInnerVert d n u) (h : (crossWiredGraphAdd d n ω D).Reachable u w) :
    IsInnerVert d n w := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h
  induction h with
  | refl => exact hu
  | tail _ hadj ih => exact crossWiredGraphAdd_adj_inner_right d n ω hD ih hadj


theorem crossWiredGraphAdd_reachable_annulus (d n : ℕ)
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {D : SimpleGraph (boxVerts d (n+1))}
    (hD : IsAnnulusWiring d n D) {u w : boxVerts d (n+1)}
    (hu : ¬ IsInnerVert d n u) (h : (crossWiredGraphAdd d n ω D).Reachable u w) :
    ¬ IsInnerVert d n w := by
  intro hw
  exact hu (crossWiredGraphAdd_reachable_inner d n ω hD hw h.symm)


end FK
end StatMech
