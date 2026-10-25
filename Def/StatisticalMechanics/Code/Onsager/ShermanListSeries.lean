/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/ShermanListSeries.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ShermanLemma4Return.Part3
import Theorem.StatisticalMechanics.Code.Onsager.ShermanListSeries


namespace StatMech.Onsager

open BigOperators

noncomputable def ons_listSeriesTerm {alpha : Type*} (wt : alpha → ℂ)
    (l : List alpha) : ℂ :=
  if h : l = [] then 0 else (l.map wt).prod / (l.length : ℂ)

end StatMech.Onsager
