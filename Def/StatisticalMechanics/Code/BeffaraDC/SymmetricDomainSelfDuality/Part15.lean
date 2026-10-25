/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/SymmetricDomainSelfDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part10
import Theorem.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality.Part6
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Abbrev.StatisticalMechanics.Code.BeffaraDC.SymmetricDomainSelfDuality.Part2
open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice


namespace StatMech

namespace BeffaraDC

noncomputable section

namespace SymmetricDomain

noncomputable def twoCoordinateSplit {E : Type*} [Fintype E] [DecidableEq E]
    (a b : E) (hab : a ≠ b) :
    (E → Bool) ≃
      Bool × (Bool × (TwoCoordinateRemainder a b hab → Bool)) :=
  (Equiv.funSplitAt a Bool).trans
    (Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.funSplitAt
        (⟨b, hab.symm⟩ : {j : E // j ≠ a}) Bool))


def boolPairTrueEquiv (R : Type*) :
    {p : Bool × (Bool × R) // p.1 = true ∧ p.2.1 = true} ≃ R where
  toFun p := p.1.2.2
  invFun r := ⟨(true, (true, r)), by simp⟩
  left_inv := by
    rintro ⟨⟨x, y, r⟩, hx, hy⟩
    change x = true at hx
    change y = true at hy
    subst x
    subst y
    rfl
  right_inv _ := rfl


noncomputable def twoCoordinateTrueEquiv {E : Type*} [Fintype E] [DecidableEq E]
    (a b : E) (hab : a ≠ b) :
    {omega : E → Bool // omega a = true ∧ omega b = true} ≃
      (TwoCoordinateRemainder a b hab → Bool) :=
  ((twoCoordinateSplit a b hab).subtypeEquiv (by
      intro omega
      simp [twoCoordinateSplit])).trans
    (boolPairTrueEquiv _)


end SymmetricDomain
end
end BeffaraDC
end StatMech
