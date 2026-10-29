/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SharpnessUnconditional.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Sharpness.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Theorem.StatisticalMechanics.Code.Percolation.PcNontrivial.Part4
import Def.StatisticalMechanics.Code.Percolation.SharpnessUnconditional
open MeasureTheory Set Filter Finset SimpleGraph
open scoped NNReal ENNReal Topology


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem lineWord_coord0 (hd : 0 < d) (k : ℕ) :
    (vertOf (lineWord hd) k) ⟨0, hd⟩ = (k : ℤ) := by
  induction k with
  | zero => simp [vertOf, origin]
  | succ j ih =>
    rw [vertOf_succ, lineWord]
    simp only [coordShift, stepSign, if_true, Function.update_self, ih]
    push_cast; ring


theorem wordEvent_measure_one (g : ℕ → Fin d × Bool) (n : ℕ) (h1 : (1 : NNReal) ≤ 1) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) 1 h1) (wordEvent g n) = 1 := by
  rw [wordEvent_eq_pi, cylinder_all_open]; simp


theorem crossProb_one (hd : 0 < d) (h1 : (1 : NNReal) ≤ 1) (n : ℕ) :
    crossProb d 1 h1 (n + 1) = 1 := by
  refine le_antisymm (crossProb_le_one d 1 h1 (n + 1)) ?_
  have hsub : wordEvent (lineWord hd) (n + 1) ⊆ crossingEvent d (n + 1) := by
    intro ω hω
    refine ⟨vertOf (lineWord hd) (n + 1), wordEvent_connected_su _ _ hω, ?_⟩
    rw [mem_box]; push Not
    refine ⟨⟨0, hd⟩, ?_⟩
    rw [lineWord_coord0 hd (n + 1)]
    have : (((n + 1 : ℕ) : ℤ)).natAbs = n + 1 := by omega
    omega
  unfold crossProb
  have hwe : (bernoulliProductMeasure (E := Sym2 (Site d)) 1 h1).real
      (wordEvent (lineWord hd) (n + 1)) = 1 := by
    rw [Measure.real, wordEvent_measure_one]; simp
  calc (1 : ℝ) = (bernoulliProductMeasure (E := Sym2 (Site d)) 1 h1).real
              (wordEvent (lineWord hd) (n + 1)) := hwe.symm
    _ ≤ (bernoulliProductMeasure (E := Sym2 (Site d)) 1 h1).real (crossingEvent d (n + 1)) :=
        measureReal_mono hsub (measure_ne_top _ _)


theorem theta_one_eq_one (hd : 0 < d) (h1 : (1 : NNReal) ≤ 1) : theta d 1 h1 = 1 := by
  have htend := tendsto_crossProb_theta (d := d) 1 h1
  have heq : (fun n => crossProb d 1 h1 (n + 1)) = (fun _ => (1 : ℝ)) := by
    funext n; exact crossProb_one hd h1 n
  rw [heq] at htend
  exact tendsto_nhds_unique htend tendsto_const_nhds


theorem theta_one_ne_zero (hd : 0 < d) : ∀ h1 : (1 : NNReal) ≤ 1, theta d 1 h1 ≠ 0 := by
  intro h1; rw [theta_one_eq_one hd h1]; norm_num


theorem hsub_unconditional :
    ∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1,
      ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n) := by
  intro p hpmem hp
  obtain ⟨hp', S, h0S, hphi⟩ := (mem_tildePcSet.mp hpmem)
  obtain ⟨N, hSN⟩ := finset_subset_box_su S
  have hSbox : (S : Set (Site d)) ⊆ box d ((N + 1) - 1) := by
    rw [Nat.add_sub_cancel]; exact hSN
  exact subcritical_decay_unconditional p hp S h0S (by rwa [Subsingleton.elim hp hp'])
    (N + 1) (by omega) hSbox


theorem sharpness_unconditional (hd : 0 < d) :
    tildePc d = pc d ∧
      (∀ p ∈ tildePcSet d, ∀ hp : p ≤ 1,
        ∃ c > 0, ∃ C > 0, ∀ n, crossProb d p hp n ≤ C * Real.exp (-c * n)) ∧
      (∀ q : NNReal, ∀ hq : q ≤ 1, tildePc d < q → (q : ℝ) < 1 →
        theta d q hq ≥ ((q : ℝ) - (tildePc d : ℝ)) / ((q : ℝ) * (1 - (tildePc d : ℝ)))) :=
  sharpness (tildePc_pos hd) (theta_one_ne_zero hd) hsub_unconditional
    (fun n _ t => deriv (crossPoly d n) t)
    (fun _q _hgt hq1 n => continuousOn_crossProbReal n (le_of_lt (tildePc_pos hd)) (le_of_lt hq1))
    (fun _q _hgt hq1 n _t ht =>
      hasDerivAt_crossProbReal n (lt_trans (tildePc_pos hd) ht.1) (lt_trans ht.2 hq1))
    (fun _q _hgt hq1 n _t ht => dct_diffineq_crossProbReal hq1 (tildePc_pos hd) n ht)

end Percolation
end StatMech
