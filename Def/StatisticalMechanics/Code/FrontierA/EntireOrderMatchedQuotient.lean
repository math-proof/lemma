/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireOrderMatchedQuotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
open Set


namespace StatMech.FrontierA

noncomputable section

def entireOrderMatchedQuotient (f g : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (f / g) Set.univ

end
end StatMech.FrontierA
