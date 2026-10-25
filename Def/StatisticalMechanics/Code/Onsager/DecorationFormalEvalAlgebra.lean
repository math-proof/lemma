/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationFormalEvalAlgebra.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationFormalSeries.Part6
import Mathlib.Analysis.Normed.Ring.InfiniteSum


namespace StatMech.Onsager

open BigOperators Finset

noncomputable def ons_mvMonomialValue
    {E : Type*} (weight : E → ℂ) (m : E →₀ ℕ) : ℂ :=
  m.prod fun edge n ↦ weight edge ^ n

end StatMech.Onsager
