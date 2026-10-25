/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/Simon.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon
open scoped BigOperators symmDiff
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false


namespace StatMech

namespace Sharpness

open Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


noncomputable def ZJ (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ) : ℝ :=
  ∑ s : ConfigSpace V, wJ E J hf s


end Sharpness
end StatMech
