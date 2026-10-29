/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteBK
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.PivotalFactorFull.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Def.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite
open MeasureTheory Set Finset
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem bk_criterion_infinite_lattice_singleton (p : NNReal) (hp : p ≤ 1)
    (Lam S : Finset (Site d)) (u x : Site d) (huS : u ∈ S) (hxS : x ∉ S) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connEvent (hypercubicLattice d) (Lam : Set (Site d)) u {x}) ≤
      ∑ q ∈ boundaryEdges d S, (p : ℝ) *
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1}) *
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connEvent (hypercubicLattice d) (Lam : Set (Site d)) q.2 {x}) := by
  classical
  let bnd := boundaryEdges d S
  let P : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1}
  let Q : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    edgeOpenEvent q.1 q.2
  let R : Site d × Site d → Set (ConfigSpace (Sym2 (Site d))) := fun q =>
    connEvent (hypercubicLattice d) (Lam : Set (Site d)) q.2 {x}
  let F := shk_firstExitSupport (d := d) S Lam
  have hPdep : ∀ q ∈ bnd, DependsOn (P q) (F : Set (Sym2 (Site d))) := by
    intro q hq
    apply (shk_connEvent_singleton_dependsOn S u q.1).mono
    intro e he
    exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
  have hQdep : ∀ q ∈ bnd, DependsOn (Q q) (F : Set (Sym2 (Site d))) := by
    intro q hq
    apply (shk_edgeOpenEvent_dependsOn q.1 q.2).mono
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst e
    apply Finset.mem_union_left
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hRdep : ∀ q ∈ bnd, DependsOn (R q) (F : Set (Sym2 (Site d))) := by
    intro q _
    apply (shk_connEvent_singleton_dependsOn Lam q.2 x).mono
    intro e he
    exact Finset.mem_union_right _ he
  have hcrit := ibk_criterion_of_finite_dependsOn hp bnd P Q R F
    hPdep hQdep hRdep
    (fun q _ => isIncreasing_connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1})
    (fun q _ => isIncreasing_edgeOpenEvent q.1 q.2)
    (fun q _ => isIncreasing_connEvent (hypercubicLattice d) (Lam : Set (Site d)) q.2 {x})
    (shk_firstExit_inclusion_lattice (Lam : Set (Site d)) S {x} u huS
      (by simpa using hxS))
  calc
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
        (connEvent (hypercubicLattice d) (Lam : Set (Site d)) u {x}) ≤
        ∑ q ∈ bnd,
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (P q) *
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (Q q) *
          (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (R q) := hcrit
    _ = ∑ q ∈ boundaryEdges d S, (p : ℝ) *
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connEvent (hypercubicLattice d) (S : Set (Site d)) u {q.1}) *
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connEvent (hypercubicLattice d) (Lam : Set (Site d)) q.2 {x}) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [show (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (Q q) =
          (p : ℝ) by
        simpa only [Q, edgeOpenEvent] using
          (coord_true_prob p hp s(q.1, q.2))]
      simp only [bnd, P, R]
      ring

end Sharpness
end StatMech
