/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingRectangularDobrushin.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.PressureBCIndep
import Theorem.StatisticalMechanics.Code.Ising.MonomialDisorder
import Instance.StatisticalMechanics.Code.FrontierA.IsingRectangularDobrushin
open scoped BigOperators
open Finset


namespace StatMech.Ising

noncomputable section

def rectangularPrismInteractionMonomial {m n h : Nat} :
    RectangularPrismInteraction m n h ->
      RectangularPrismConfig m n h -> Real
  | .inl q, sigma =>
      rectangularPrismSpin sigma ⟨q.1.val, by omega⟩ q.2.1 q.2.2 *
        rectangularPrismSpin sigma ⟨q.1.val + 1, by omega⟩ q.2.1 q.2.2
  | .inr (.inl q), sigma =>
      rectangularPrismSpin sigma q.1 ⟨q.2.1.val, by omega⟩ q.2.2 *
        rectangularPrismSpin sigma q.1 ⟨q.2.1.val + 1, by omega⟩ q.2.2
  | .inr (.inr (.inl q)), sigma =>
      rectangularPrismSpin sigma q.1 q.2.1 ⟨q.2.2.val, by omega⟩ *
        rectangularPrismSpin sigma q.1 q.2.1 ⟨q.2.2.val + 1, by omega⟩
  | .inr (.inr (.inr v)), sigma => spin sigma v


def rectangularPrismInteractionCoupling
    (J beta : Real) {m n h : Nat} :
    RectangularPrismInteraction m n h -> Real
  | .inl _ => beta * J
  | .inr (.inl _) => beta * J
  | .inr (.inr (.inl _)) => beta * J
  | .inr (.inr (.inr v)) => beta * J * rectangularPrismBoundaryDegree v


noncomputable def rectangularPrismDisorderSheet (m n h : Nat) :
    Finset (RectangularPrismInteraction m n h) := by
  classical
  exact Finset.univ.filter fun q => match q with
    | .inr (.inr (.inl z)) => z.2.2.val = h
    | _ => false

end
end StatMech.Ising
