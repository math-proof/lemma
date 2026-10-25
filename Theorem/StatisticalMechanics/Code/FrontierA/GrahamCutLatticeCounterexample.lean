/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCutLatticeCounterexample.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Instance.StatisticalMechanics.Code.FrontierA.GrahamCutLatticeCounterexample.Part3
open Finset


namespace StatMech.FrontierA

theorem grahamC4RootCutSupported_empty :
    GrahamC4RootCutSupported ∅ := by decide

theorem grahamC4RootCutSupported_one :
    GrahamC4RootCutSupported {1} := by decide

theorem grahamC4RootCutSupported_two :
    GrahamC4RootCutSupported {2} := by decide

theorem not_grahamC4RootCutSupported_one_two :
    ¬ GrahamC4RootCutSupported {1, 2} := by decide


theorem grahamC4_rootCutSupport_not_unionClosed :
    ∃ A B : Finset (Fin 4),
      GrahamC4RootCutSupported A /\
      GrahamC4RootCutSupported B /\
      GrahamC4RootCutSupported (A ∩ B) /\
      ¬ GrahamC4RootCutSupported (A ∪ B) := by
  refine ⟨{1}, {2}, grahamC4RootCutSupported_one,
    grahamC4RootCutSupported_two, ?_, ?_⟩
  · simpa using grahamC4RootCutSupported_empty
  · simpa using not_grahamC4RootCutSupported_one_two


theorem grahamC4_not_latticeCondition_of_exact_cutSupport
    (mu : Finset (Fin 4) -> Real)
    (hmu : ∀ S, 0 <= mu S)
    (hsupport : ∀ S, 0 < mu S <-> GrahamC4RootCutSupported S) :
    ¬ ∀ A B : Finset (Fin 4),
      mu A * mu B <= mu (A ∩ B) * mu (A ∪ B) := by
  intro hlattice
  have h1 : 0 < mu {1} :=
    (hsupport {1}).2 grahamC4RootCutSupported_one
  have h2 : 0 < mu {2} :=
    (hsupport {2}).2 grahamC4RootCutSupported_two
  have huNotPos : ¬ 0 < mu {1, 2} := by
    intro hu
    exact not_grahamC4RootCutSupported_one_two ((hsupport {1, 2}).1 hu)
  have hu : mu {1, 2} = 0 := by
    exact le_antisymm (le_of_not_gt huNotPos) (hmu {1, 2})
  have h := hlattice {1} {2}
  have hi : ({1} ∩ {2} : Finset (Fin 4)) = ∅ := by decide
  have huu : ({1} ∪ {2} : Finset (Fin 4)) = {1, 2} := by decide
  rw [hi, huu, hu, mul_zero] at h
  exact (not_lt_of_ge h) (mul_pos h1 h2)


end StatMech.FrontierA
