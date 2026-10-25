/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Strassen.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.StochasticDomination
import Def.StatisticalMechanics.Code.Foundations.Strassen
open MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

variable {E : Type*}


structure MonotoneCoupling (μ ν : Measure (ConfigSpace E))
    (κ : Measure (ConfigSpace E × ConfigSpace E)) : Prop where
  
  fst_eq : κ.fst = μ
  
  snd_eq : κ.snd = ν
  
  supported : κ (orderSet E)ᶜ = 0

end StatMech
