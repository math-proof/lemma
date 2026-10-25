/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/SpliceST1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.TailSelMPClose.Part2
import Abbrev.StatisticalMechanics.Code.OSSS.SpliceST1
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open OSSS.Monotonic OSSS.Coding OSSS.GrandCoupling OSSS.GrandCouplingAssembly

open StatMech.Probability OSSS.AdaptiveTau OSSS.AdaptMConditional

variable {E : Type*} [Fintype E] [DecidableEq E]


def sp1_idxEq (n t : ℕ) :
    {j : {i : Fin n // ¬ (i:ℕ) < t} // ¬ (((j : {i : Fin n // ¬ (i:ℕ) < t}) : Fin n) : ℕ) < t+1}
      ≃ {i : Fin n // ¬ (i:ℕ) < t+1} where
  toFun := fun j => ⟨(j.1 : Fin n), j.2⟩
  invFun := fun i => ⟨⟨(i : Fin n), by have := i.2; omega⟩, i.2⟩
  left_inv := by intro j; rfl
  right_inv := by intro i; rfl


noncomputable def sp1_renTail (n t : ℕ) :
    ({j : {i : Fin n // ¬ (i:ℕ) < t} // ¬ (((j : {i : Fin n // ¬ (i:ℕ) < t}) : Fin n) : ℕ) < t+1} → ℝ)
      ≃ᵐ ({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : {i : Fin n // ¬ (i:ℕ) < t+1} => ℝ) (sp1_idxEq n t)


noncomputable def sp1_tailDisint (n t : ℕ) :
    ({i : Fin n // ¬ (i:ℕ) < t} → ℝ) ≃ᵐ
      (({i : Fin n // ¬ (i:ℕ) < t+1} → ℝ) × (sp1_Sing n t → ℝ)) :=
  (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : {i : Fin n // ¬ (i:ℕ) < t} => ℝ)
      (fun j => ¬ (((j : {i : Fin n // ¬ (i:ℕ) < t}) : Fin n) : ℕ) < t+1)).trans
    (MeasurableEquiv.prodCongr (sp1_renTail n t) (MeasurableEquiv.refl (sp1_Sing n t → ℝ)))

end AdaptDisintegration
end OSSS
end StatMech
