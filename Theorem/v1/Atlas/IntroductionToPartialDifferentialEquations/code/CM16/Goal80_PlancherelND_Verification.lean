/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/IntroductionToPartialDifferentialEquations/code/CM16/Goal80_PlancherelND_Verification.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
import Lemma.Real.Atlas.v1.IntroductionToPartialDifferentialEquations.code.CM16.FourierTransform
open FourierAnalysis


#check @fourier_inversionND


#check @fourier_inner_swapND


#check @plancherelND


#check @plancherel_ft_memLpND


#check @plancherel_normND


