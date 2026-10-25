/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.Umlaufsatz.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EnclosedAreaWitness.Part3
import Theorem.StatisticalMechanics.Code.Lattice.StarHullWinding.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingEarInduction.Part3
import Def.StatisticalMechanics.Code.Lattice.LexMinOrientation
open Set SimpleGraph Function


namespace StatMech

namespace Lattice

theorem lmo_lexMinCell (K : Set (Site 2)) (hK : K.Finite) (hne : K.Nonempty) :
    ∃ z₀ ∈ K, (![z₀ 0 - 1, z₀ 1] : Site 2) ∉ K ∧ (![z₀ 0, z₀ 1 - 1] : Site 2) ∉ K ∧
      (∀ w ∈ K, z₀ 0 ≤ w 0) := by
  classical
  have hKf : hK.toFinset.Nonempty := by rw [Set.Finite.toFinset_nonempty]; exact hne
  obtain ⟨z₀, hz₀mem, hz₀min⟩ := hK.toFinset.exists_min_image lmo_lexKey hKf
  rw [Set.Finite.mem_toFinset] at hz₀mem
  have hmin : ∀ w ∈ K, lmo_lexKey z₀ ≤ lmo_lexKey w := fun w hw =>
    hz₀min w (Set.Finite.mem_toFinset _ |>.mpr hw)
  refine ⟨z₀, hz₀mem, ?_, ?_, ?_⟩
  · intro hin
    have := hmin _ hin
    rw [lmo_lexKey, lmo_lexKey] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [Prod.Lex.le_iff] at this; simp only [ofLex_toLex] at this
    rcases this with h | h
    · omega
    · omega
  · intro hin
    have := hmin _ hin
    rw [lmo_lexKey, lmo_lexKey] at this
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at this
    rw [Prod.Lex.le_iff] at this; simp only [ofLex_toLex] at this
    rcases this with h | h
    · omega
    · obtain ⟨_, h2⟩ := h; omega
  · intro w hw
    have := hmin w hw
    rw [lmo_lexKey, lmo_lexKey] at this
    rw [Prod.Lex.le_iff] at this; simp only [ofLex_toLex] at this
    rcases this with h | h
    · omega
    · obtain ⟨h1, _⟩ := h; omega


end Lattice
end StatMech
