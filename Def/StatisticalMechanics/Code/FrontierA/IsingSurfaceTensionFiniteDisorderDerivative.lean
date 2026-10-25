/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionFiniteDisorderDerivative.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel.Part4
open scoped BigOperators
open Finset


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


def multibondBondSpin (ends : P -> V × V) (s : V -> Bool) (p : P) : Real :=
  if s (ends p).1 = s (ends p).2 then 1 else -1


def multibondTotalBondSpin (ends : P -> V × V) (s : V -> Bool) : Real :=
  ∑ p : P, multibondBondSpin ends s p


def multibondTwistedBondSpin
    (ends : P -> V × V) (D : Finset P) (s : V -> Bool) : Real :=
  ∑ p : P, (if p ∈ D then (-1 : Real) else 1) * multibondBondSpin ends s p


def multibondMeanTotalBondSpin (ends : P -> V × V) (J : Real) : Real :=
  (∑ s : V -> Bool,
      multibondIsingWeight ends (fun _ => J) s * multibondTotalBondSpin ends s) /
    multibondIsingPartition ends (fun _ => J)


def multibondMeanTwistedBondSpin
    (ends : P -> V × V) (D : Finset P) (J : Real) : Real :=
  (∑ s : V -> Bool,
      multibondIsingWeight ends (multibondTwistCoupling (fun _ => J) D) s *
        multibondTwistedBondSpin ends D s) /
    multibondIsingPartition ends (multibondTwistCoupling (fun _ => J) D)

end
end StatMech.FrontierA
