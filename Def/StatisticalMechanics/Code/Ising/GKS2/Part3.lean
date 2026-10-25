/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part3
open scoped BigOperators symmDiff
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


def dblEquiv : (ConfigSpace V × ConfigSpace V) ≃ (ConfigSpace V × ConfigSpace V) where
  toFun := dblFun
  invFun := dblFun
  left_inv := dblFun_invol
  right_inv := dblFun_invol


end Ising
end StatMech
