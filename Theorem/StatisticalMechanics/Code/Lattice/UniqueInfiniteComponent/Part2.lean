/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/UniqueInfiniteComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Def.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part2
open Set SimpleGraph


namespace StatMech

namespace Lattice

variable {d : ℕ}


@[simp]
theorem setOn_empty (p : Site d) (v : ℤ) : setOn p ∅ v = p := by funext k; simp [setOn]

theorem setOn_insert (p : Site d) (T : Finset (Fin d)) (j : Fin d) (v : ℤ) (hj : j ∉ T) :
    setOn p (insert j T) v = Function.update (setOn p T v) j v := by
  funext k
  simp only [setOn, Function.update]
  by_cases hk : k = j
  · subst hk; simp [hj]
  · simp [hk, Finset.mem_insert]

theorem setOn_notMem (p : Site d) (T : Finset (Fin d)) (v : ℤ) {i0 : Fin d} (h : i0 ∉ T) :
    setOn p T v i0 = p i0 := by simp [setOn, h]


theorem exterior_reachable_setOn (R : ℕ) (p : Site d) (i0 : Fin d)
    (hi0 : R < (p i0).natAbs) (T : Finset (Fin d)) (hT : i0 ∉ T)
    (hpext : p ∈ exterior d R) (htgt : setOn p T ((R : ℤ) + 1) ∈ exterior d R) :
    ((hypercubicLattice d).induce (exterior d R)).Reachable ⟨p, hpext⟩
      ⟨setOn p T ((R : ℤ) + 1), htgt⟩ := by
  induction T using Finset.induction_on with
  | empty =>
    have heq : (⟨setOn p ∅ ((R : ℤ) + 1), htgt⟩ : exterior d R) = ⟨p, hpext⟩ :=
      Subtype.ext (setOn_empty p ((R : ℤ) + 1))
    rw [heq]
  | insert j T hjT ih =>
    have hi0T : i0 ∉ T := fun h => hT (Finset.mem_insert_of_mem h)
    have hji0 : j ≠ i0 := fun h => hT (h ▸ Finset.mem_insert_self j T)
    set q := setOn p T ((R : ℤ) + 1) with hq
    have hqi0 : q i0 = p i0 := setOn_notMem p T _ hi0T
    have hqext : q ∈ exterior d R := ⟨i0, by rw [hqi0]; exact hi0⟩
    have hstep_tgt : Function.update q j ((R : ℤ) + 1) ∈ exterior d R := by
      refine ⟨i0, ?_⟩; rw [Function.update_of_ne (Ne.symm hji0), hqi0]; exact hi0
    have hseg : ∀ z : ℤ, (min (q j) ((R : ℤ) + 1) ≤ z ∧ z ≤ max (q j) ((R : ℤ) + 1)) →
        Function.update q j z ∈ exterior d R := by
      intro z _
      refine ⟨i0, ?_⟩; rw [Function.update_of_ne (Ne.symm hji0), hqi0]; exact hi0
    have step := segment_gen (exterior d R) j q ((R : ℤ) + 1) hqext hstep_tgt hseg
    have hchain := (ih hi0T hqext).trans step
    have hval : setOn p (insert j T) ((R : ℤ) + 1) = Function.update q j ((R : ℤ) + 1) :=
      setOn_insert p T j ((R : ℤ) + 1) hjT
    have heq : (⟨setOn p (insert j T) ((R : ℤ) + 1), htgt⟩ : exterior d R)
        = ⟨Function.update q j ((R : ℤ) + 1), hstep_tgt⟩ := Subtype.ext hval
    rw [heq]; exact hchain


end Lattice
end StatMech
