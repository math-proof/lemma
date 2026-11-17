/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/EntireOrderMatchedQuotient.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Meromorphic.NormalForm

@[expose] public section

open Set


namespace StatMech.FrontierA

noncomputable section

def entireOrderMatchedQuotient (f g : ℂ → ℂ) : ℂ → ℂ :=
  toMeromorphicNFOn (f / g) Set.univ

end
end StatMech.FrontierA
