/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part6
open Finset


namespace StatMech.FrontierA

theorem grahamK23RootCutSupported_zero_two :
    GrahamK23RootCutSupported {0, 2} := by decide

theorem grahamK23RootCutSupported_one_two :
    GrahamK23RootCutSupported {1, 2} := by decide

theorem grahamK23RootCutSupported_two :
    GrahamK23RootCutSupported {2} := by decide

theorem not_grahamK23RootCutSupported_zero_one_two :
    ¬ GrahamK23RootCutSupported {0, 1, 2} := by decide

theorem grahamK23_pair_reaches_in_left_cut :
    grahamK23ReachWithin {0, 2} 0 2 := by decide

theorem grahamK23_pair_reaches_in_right_cut :
    grahamK23ReachWithin {1, 2} 2 1 := by decide


theorem grahamK23_not_rawCutFourFunctions_of_exactSupport
    (mu f g : Finset (Fin 5) -> Real)
    (hmu : ∀ S, 0 <= mu S)
    (hsupport : ∀ S, 0 < mu S <-> GrahamK23RootCutSupported S)
    (hf : 0 < f {0, 2}) (hg : 0 < g {1, 2}) :
    ¬ ∀ A B : Finset (Fin 5),
      (mu A * f A) * (mu B * g B) <=
        mu (A ∩ B) * (mu (A ∪ B) * (f (A ∪ B) * g (A ∪ B))) := by
  intro hfour
  have hA : 0 < mu {0, 2} :=
    (hsupport {0, 2}).2 grahamK23RootCutSupported_zero_two
  have hB : 0 < mu {1, 2} :=
    (hsupport {1, 2}).2 grahamK23RootCutSupported_one_two
  have huNotPos : ¬ 0 < mu {0, 1, 2} := by
    intro hu
    exact not_grahamK23RootCutSupported_zero_one_two
      ((hsupport {0, 1, 2}).1 hu)
  have hu : mu {0, 1, 2} = 0 :=
    le_antisymm (le_of_not_gt huNotPos) (hmu {0, 1, 2})
  have h := hfour {0, 2} {1, 2}
  have hi : ({0, 2} ∩ {1, 2} : Finset (Fin 5)) = {2} := by decide
  have huu : ({0, 2} ∪ {1, 2} : Finset (Fin 5)) = {0, 1, 2} := by decide
  rw [hi, huu, hu, zero_mul, mul_zero] at h
  exact (not_lt_of_ge h) (mul_pos (mul_pos hA hf) (mul_pos hB hg))

end StatMech.FrontierA
