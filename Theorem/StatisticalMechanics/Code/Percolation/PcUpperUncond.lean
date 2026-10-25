/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcUpperUncond.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpper.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
open MeasureTheory Filter Topology Finset Set SimpleGraph
open scoped NNReal ENNReal BigOperators


namespace StatMech

namespace Percolation

open StatMech.Lattice


theorem cylinder_all_closed {d : ℕ} (p : ℝ≥0) (hp : p ≤ 1) (F : Finset (Sym2 (Site d))) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp)
      ((F : Set (Sym2 (Site d))).pi (fun _ => ({false} : Set Bool)))
      = ((1 - p : ℝ≥0) : ℝ≥0∞) ^ F.card := by
  have key := Measure.infinitePi_pi (μ := fun _ : Sym2 (Site d) => bernoulliMeasure p hp)
    (s := F) (t := fun _ => ({false} : Set Bool)) (fun i _ => measurableSet_singleton _)
  rw [bernoulliProductMeasure, key]
  simp only [bernoulliMeasure_apply_false]
  rw [Finset.prod_const]


theorem sharedPrimalEdge_right' (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a + 1, b] = s(![a + 1, b], ![a + 1, b + 1]) := by
  rw [sharedPrimalEdge_right]; rfl


theorem sharedPrimalEdge_left' (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a - 1, b] = s(![a, b], ![a, b + 1]) := by
  rw [sharedPrimalEdge_left]; rfl


theorem sharedPrimalEdge_top' (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a, b + 1] = s(![a, b + 1], ![a + 1, b + 1]) := by
  rw [sharedPrimalEdge_top]; rfl


theorem sharedPrimalEdge_bottom' (a b : ℤ) :
    sharedPrimalEdge ![a, b] ![a, b - 1] = s(![a, b], ![a + 1, b]) := by
  rw [sharedPrimalEdge_bottom]; rfl


theorem face_adj_dir {f g : Site 2} (h : (hypercubicLattice 2).Adj f g) :
    (g = ![f 0 + 1, f 1]) ∨ (g = ![f 0 - 1, f 1]) ∨
      (g = ![f 0, f 1 + 1]) ∨ (g = ![f 0, f 1 - 1]) := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at h
  by_cases h0 : f 0 = g 0
  · have hg1 : g 1 = f 1 + 1 ∨ g 1 = f 1 - 1 := by omega
    have hgform : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
    rcases hg1 with hh | hh
    · right; right; left; rw [hgform, ← h0, hh]
    · right; right; right; rw [hgform, ← h0, hh]
  · have h1 : f 1 = g 1 := by
      by_contra hne
      have : (f 0 - g 0).natAbs ≥ 1 := by omega
      have : (f 1 - g 1).natAbs ≥ 1 := by omega
      omega
    have hg0 : g 0 = f 0 + 1 ∨ g 0 = f 0 - 1 := by omega
    have hgform : g = ![g 0, g 1] := by funext i; fin_cases i <;> rfl
    rcases hg0 with hh | hh
    · left; rw [hgform, ← h1, hh]
    · right; left; rw [hgform, ← h1, hh]


theorem sharedPrimalEdge_uncrossInj {f g f' g' : Site 2}
    (h : (hypercubicLattice 2).Adj f g) (h' : (hypercubicLattice 2).Adj f' g')
    (heq : sharedPrimalEdge f g = sharedPrimalEdge f' g') : s(f, g) = s(f', g') := by
  have hf : f = ![f 0, f 1] := by funext i; fin_cases i <;> rfl
  have hf' : f' = ![f' 0, f' 1] := by funext i; fin_cases i <;> rfl
  rcases face_adj_dir h with hg | hg | hg | hg <;>
  rcases face_adj_dir h' with hg' | hg' | hg' | hg' <;>
    (rw [hf, hg] at heq; rw [hf', hg'] at heq;
     rw [hf, hg, hf', hg'];
     simp only [sharedPrimalEdge_right', sharedPrimalEdge_left', sharedPrimalEdge_top',
                sharedPrimalEdge_bottom', Sym2.eq_iff, site2_eq] at heq ⊢;
     omega)


end Percolation
end StatMech
