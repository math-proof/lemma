/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/UBlockFactor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.AdaptDisintegration.Part4
import Instance.StatisticalMechanics.Code.OSSS.UBlockFactor
open scoped BigOperators ENNReal
open Finset MeasureTheory

set_option linter.style.longLine false
set_option linter.unusedSectionVars false


namespace StatMech

namespace OSSS

namespace AdaptDisintegration

open StatMech.Probability


noncomputable def ubfSplit (n t : ℕ) :
    (Fin n → ℝ) ≃ᵐ
      (({i : Fin n // (i : ℕ) < t} → ℝ) × ({i : Fin n // ¬ (i : ℕ) < t} → ℝ)) :=
  MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) (fun i => (i : ℕ) < t)


end AdaptDisintegration
end OSSS
end StatMech
