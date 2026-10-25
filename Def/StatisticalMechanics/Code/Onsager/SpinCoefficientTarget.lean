/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCoefficientTarget.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
import Theorem.StatisticalMechanics.Code.Onsager.SpinPolynomial.Part4
import Theorem.StatisticalMechanics.Code.Onsager.SpinCoefficientTarget


namespace StatMech.Onsager

open Matrix BigOperators

def ons_spinCoefficientIdentity (L : ℕ) [Fact (2 < L)] (x : ℝ) : Prop :=
  ∀ a b : Fin 2,
    (ons_spinCharacterSum L x a b : ℂ) ^ 2 =
      (1 - ons_KWmatPhase L (x : ℂ) ons_turnRoot
        (ons_spinPhase L a) (ons_spinPhase L b)).det

end StatMech.Onsager
