/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/PcNontrivial.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Theta
import Def.StatisticalMechanics.Code.Percolation.TildePc.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Def.StatisticalMechanics.Code.Percolation.PcNontrivial.Part2
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal
open Finset

set_option linter.deprecated false
set_option linter.style.longLine false


namespace StatMech

namespace Percolation

open StatMech.Lattice

variable {d : ℕ}


theorem edgeOf_injOn (g : ℕ → Fin d × Bool) (n : ℕ) (hg : goodWord g n) :
    Set.InjOn (edgeOf g) (Finset.range n) := by
  intro k hk l hl hkl
  simp only [Finset.coe_range, Set.mem_Iio] at hk hl
  have hmem : ∀ m, m ≤ n → (m : ℕ) ∈ ((Finset.range (n + 1) : Finset ℕ) : Set ℕ) := by
    intro m hm; simp only [Finset.coe_range, Set.mem_Iio]; omega
  unfold edgeOf at hkl
  rw [Sym2.eq_iff] at hkl
  rcases hkl with ⟨h1, _⟩ | ⟨h1, h2⟩
  · exact hg (hmem k (by omega)) (hmem l (by omega)) h1
  · have e1 : k = l + 1 := hg (hmem k (by omega)) (hmem (l + 1) (by omega)) h1
    have e2 : k + 1 = l := hg (hmem (k + 1) (by omega)) (hmem l (by omega)) h2
    omega


theorem wordEvent_eq_pi (g : ℕ → Fin d × Bool) (n : ℕ) :
    wordEvent g n
      = (((Finset.range n).image (edgeOf g) : Finset (Sym2 (Site d))) :
          Set (Sym2 (Site d))).pi (fun _ => ({true} : Set Bool)) := by
  ext ω
  simp only [wordEvent, Set.mem_setOf_eq, Set.mem_pi, Finset.coe_image, Finset.coe_range,
    Set.mem_image, Set.mem_Iio, Set.mem_singleton_iff, forall_exists_index, and_imp]
  constructor
  · intro h e k hk hek; subst hek; exact h k (by simp [hk])
  · intro h k hk; exact h (edgeOf g k) k (by simpa using hk) rfl


theorem wordEvent_prob_good (p : ℝ≥0) (hp : p ≤ 1) (g : ℕ → Fin d × Bool) (n : ℕ)
    (hg : goodWord g n) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp) (wordEvent g n) = (p : ℝ≥0∞) ^ n := by
  rw [wordEvent_eq_pi, cylinder_all_open]
  congr 1
  rw [Finset.card_image_of_injOn (edgeOf_injOn g n hg), Finset.card_range]


end Percolation
end StatMech
