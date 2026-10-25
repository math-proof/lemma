/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/TurningNumber.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Def.StatisticalMechanics.Code.Lattice.TurningNumber
open SimpleGraph Function


namespace StatMech

namespace Lattice

@[simp] theorem rotPow_zero (x : Site 2) : rotPow 0 x = x := rfl

@[simp] theorem rotPow_one (x : Site 2) : rotPow 1 x = rot90Fun x := rfl


theorem rotPow_two (x : Site 2) : rotPow 2 x = -x := by
  show rot90Fun^[(2 : ZMod 4).val] x = -x
  have h : (2 : ZMod 4).val = 2 := by decide
  rw [h]; exact rot90Fun_rot90Fun x


theorem rotPow_three (x : Site 2) : rotPow 3 x = -rot90Fun x := by
  show rot90Fun^[(3 : ZMod 4).val] x = -rot90Fun x
  have h : (3 : ZMod 4).val = 3 := by decide
  rw [h]; show rot90Fun (rot90Fun (rot90Fun x)) = -rot90Fun x
  rw [rot90Fun_rot90Fun']


theorem rotPow_add (a b : ZMod 4) (x : Site 2) :
    rotPow (a + b) x = rotPow a (rotPow b x) := by
  unfold rotPow
  rw [← Function.iterate_add_apply, rot90Fun_iterate_mod (a.val + b.val),
    rot90Fun_iterate_mod (a + b).val, ZMod.val_add, Nat.mod_mod]


theorem neg_dartDir_ne_dartDir (e : Dart) : -e.dir ≠ e.dir := by
  intro h
  apply dartDir_ne_zero e
  funext i
  have hi := congrFun h i
  simp only [Pi.neg_apply, Pi.zero_apply] at hi ⊢
  omega


theorem zmod4_cases (s : ZMod 4) : s = 0 ∨ s = 1 ∨ s = 2 ∨ s = 3 := by decide +revert


theorem rotPow_dir_eq_iff (e : Dart) (s : ZMod 4) :
    rotPow s e.dir = e.dir ↔ s = 0 := by
  constructor
  · intro h
    rcases zmod4_cases s with h0 | h1 | h2 | h3
    · exact h0
    · subst h1; rw [rotPow_one] at h; exact absurd h (rot90Fun_dartDir_ne_dartDir e)
    · subst h2; rw [rotPow_two] at h; exact absurd h (neg_dartDir_ne_dartDir e)
    · subst h3; rw [rotPow_three] at h; exact absurd h (neg_rot90Fun_dartDir_ne_dartDir e)
  · rintro rfl; rfl


end Lattice
end StatMech
