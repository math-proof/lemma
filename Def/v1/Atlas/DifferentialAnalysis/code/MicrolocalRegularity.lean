/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/MicrolocalRegularity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.DifferentialAnalysis.code.WavefrontSet.Part3
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.WavefrontSet
import Lemma.Real.Atlas.v1.DifferentialAnalysis.code.ConeSupportCorollary
import Theorem.v1.Atlas.DifferentialAnalysis.code.ConeSupportCorollary
import Theorem.v1.Atlas.DifferentialAnalysis.code.MicrolocalRegularity


noncomputable section

open scoped SchwartzMap

namespace WavefrontSet

variable {n : ℕ}


/-- When the conic singular support `Css u` of a tempered distribution is empty, produce a Schwartz
function whose Schwartz embedding equals `u`. -/
def toSchwartzOfEmptyCss {n : ℕ}
    (u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ))
    (h : Css u = ∅) : SchwartzMap (EuclideanSpace ℝ (Fin n)) ℂ :=
  ((ConeSupport.coneSingularSupport_eq_empty_iff u).mp
    (coneSingularSupport_empty_of_Css_empty u h)).choose

end WavefrontSet
end
