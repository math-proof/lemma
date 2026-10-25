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
import Def.StatisticalMechanics.Code.FK.BoxCrossGraph.Part13
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false


namespace StatMech

namespace FK

open StatMech.Lattice


theorem condFibre_eq_image_crossExt (d n : ℕ) :
    condFibre (innerEdgeFinset d n) (fun _ => false)
      = Finset.univ.image (crossExt d n) := by
  ext ρ
  rw [mem_condFibre, Finset.mem_image]
  constructor
  · intro hρ
    exact ⟨innerRestrict d n ρ, Finset.mem_univ _, crossExt_innerRestrict_of_agreesOff d n hρ⟩
  · rintro ⟨ω, _, rfl⟩
    exact agreesOff_crossExt d n ω


theorem inducedBcZ_innerEdgeFinset (d n : ℕ) {p q : ℝ} :
    inducedBcZ (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n)) p q
        (innerEdgeFinset d n) (fun _ => false)
      = wiredFkZ (boxGraph d n) (boxBoundary d n) p q * crossShift d n p q := by
  rw [inducedBcZ, condFibre_eq_image_crossExt,
    Finset.sum_image (fun a _ b _ h => by
      have := congrArg (innerRestrict d n) h
      rwa [innerRestrict_crossExt, innerRestrict_crossExt] at this),
    wiredFkZ, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun ω _ => bcWeight_crossExt d n ω)


theorem condBcProb_crossExt_eq_wiredFkProb (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    condBcProb (boxGraph d (n+1))
        (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n)) p q
        (innerEdgeFinset d n) (fun _ => false) (crossExt d n ω)
      = wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  rw [condBcProb, if_pos (agreesOff_crossExt d n ω), bcWeight_crossExt,
    inducedBcZ_innerEdgeFinset, wiredFkProb]
  rw [mul_div_mul_right _ _ (crossShift_pos hp1 hq).ne']


theorem boxBoundary_succ_iff_not_inner (d n : ℕ) (v : boxVerts d (n+1)) :
    boxBoundary d (n+1) v ↔ ¬ IsInnerVert d n v := by
  unfold boxBoundary IsInnerVert
  rw [StatMech.Lattice.mem_vertexBoundary, Nat.add_sub_cancel]
  constructor
  · rintro ⟨_, hnotin⟩; exact hnotin
  · intro hnotin; exact ⟨v.2, hnotin⟩


end FK
end StatMech
