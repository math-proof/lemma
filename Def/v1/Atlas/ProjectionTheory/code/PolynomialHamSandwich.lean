/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/PolynomialHamSandwich.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.ProjectionTheory.code.BorsukUlam
import Lemma.Real.Atlas.v1.ProjectionTheory.code.BorsukUlam
open MeasureTheory MvPolynomial


noncomputable section

namespace PolynomialHamSandwich

/-- A polynomial `P : ℝ[x₁, …, x_d]` *bisects* a measurable set `U ⊆ ℝ^d` if the
parts of `U` where `P > 0` and where `P < 0` have equal Lebesgue volume. -/
def Bisects (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ)) : Prop :=
  volume ({x ∈ U | eval x P > 0}) =
    volume ({x ∈ U | eval x P < 0})

/-- The signed volume `vol{P > 0 in U} − vol{P < 0 in U}` as a real number; this
function is zero exactly when `P` bisects `U` (assuming `U` is bounded). -/
def signedVol (d : ℕ) (P : MvPolynomial (Fin d) ℝ) (U : Set (Fin d → ℝ)) : ℝ :=
  (volume ({x ∈ U | eval x P > 0})).toReal -
    (volume ({x ∈ U | eval x P < 0})).toReal

end PolynomialHamSandwich
end
