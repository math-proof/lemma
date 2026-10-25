/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/wnaalternate.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.GaussBonnet.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.WindingWitness.Part4
import Theorem.StatisticalMechanics.Code.Walls.umffullrev.Part2
import Theorem.StatisticalMechanics.Code.Walls.wndwinding.Part3
import Theorem.StatisticalMechanics.Code.Walls.wnuupperhalf.Part5
import Def.StatisticalMechanics.Code.Walls.wnaalternate
open Finset Set SimpleGraph
open scoped BigOperators


namespace StatMech

namespace Lattice

theorem wna_alt_of_prefix_in_01 :
    ∀ (L : List ℤ) (s : ℤ), (s = 0 ∨ s = 1) →
      (∀ x ∈ L, x = 1 ∨ x = -1) →
      (∀ p ∈ (L.scanl (· + ·) s), p = 0 ∨ p = 1) →
      wnu_Alt L := by
  intro L
  induction L with
  | nil => intro s _ _ _; exact trivial
  | cons a t ih =>
    intro s hs hpm hall
    have ha0 : a = 1 ∨ a = -1 := hpm a (by simp)
    have hscan : (a :: t).scanl (· + ·) s = s :: t.scanl (· + ·) (s + a) :=
      List.scanl_cons
    
    have hsa_in : (s + a) = 0 ∨ (s + a) = 1 := by
      apply hall
      rw [hscan]
      refine List.mem_cons_of_mem _ ?_
      cases t with
      | nil => rw [List.scanl_nil]; simp
      | cons b t' => rw [List.scanl_cons]; simp
    cases t with
    | nil => exact ha0
    | cons b t' =>
      have hb0 : b = 1 ∨ b = -1 := hpm b (by simp)
      refine ⟨ha0, ?_, ?_⟩
      · 
        have hsab_in : (s + a + b) = 0 ∨ (s + a + b) = 1 := by
          apply hall
          rw [hscan, List.scanl_cons]
          refine List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ?_)
          cases t' with
          | nil => rw [List.scanl_nil]; simp
          | cons c t'' => rw [List.scanl_cons]; simp
        rcases hsa_in with h | h <;> rcases hsab_in with h' | h' <;>
          rcases ha0 with ha | ha <;> rcases hb0 with hb | hb <;> omega
      · 
        apply ih (s + a) hsa_in
        · intro x hx; exact hpm x (by simp [hx])
        · intro p hp
          apply hall
          rw [hscan]
          exact List.mem_cons_of_mem _ hp


theorem wna_alt_of_prefixSums_in_01 (L : List ℤ)
    (hpm : ∀ x ∈ L, x = 1 ∨ x = -1)
    (hpref : ∀ p ∈ wna_prefixSums L, p = 0 ∨ p = 1) :
    wnu_Alt L := by
  apply wna_alt_of_prefix_in_01 L 0 (Or.inl rfl) hpm
  intro p hp
  
  rw [show L.scanl (· + ·) 0 = 0 :: wna_prefixSums L from ?_] at hp
  · rcases List.mem_cons.mp hp with h | h
    · left; exact h
    · exact hpref p h
  · unfold wna_prefixSums
    cases L with
    | nil => simp
    | cons a t => rw [List.scanl_cons]; simp


end Lattice
end StatMech
