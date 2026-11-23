/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/Goal80_PlancherelND_Verification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
public import Theorem.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
open FourierAnalysis

public section

#check @fourier_inversionND


#check @fourier_inner_swapND


#check @plancherelND


#check @plancherel_ft_memLpND


#check @plancherel_normND


