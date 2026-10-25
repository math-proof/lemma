/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Inequalities/ReimerFiberClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Reimer.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerFiberClose
open MeasureTheory Finset
open scoped NNReal BigOperators


namespace StatMech

open ConfigSpace

variable {E : Type*}


section Fintype

variable [Fintype E] [DecidableEq E]

noncomputable def detIndicatorP (A : Set (ConfigSpace E)) (p : E → Prop)
    [DecidablePred p] (a : {x // p x} → Bool) : ℝ :=
  A.indicator (fun _ => (1 : ℝ))
    ((Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (a, fun _ => false))


noncomputable def detIndicatorNP (B : Set (ConfigSpace E)) (p : E → Prop)
    [DecidablePred p] (b : {x // ¬ p x} → Bool) : ℝ :=
  B.indicator (fun _ => (1 : ℝ))
    ((Equiv.piEquivPiSubtypeProd p (fun _ : E => Bool)).symm (fun _ => false, b))

end Fintype
end StatMech
