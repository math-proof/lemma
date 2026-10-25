/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareSwitching
open Complex


namespace StatMech.Universality

noncomputable section

def IsingSquareSHolomorphicQuad (A B C D : Complex) : Prop :=
  A - B = (starRingEnd Complex) A - (starRingEnd Complex) B ∧
  C - D = (starRingEnd Complex) D - (starRingEnd Complex) C ∧
  A - C = Complex.I * (D - B)


def isingPrimitiveSquareCombination (A B C D : Complex) : Complex :=
  A ^ 2 + Complex.I * B ^ 2 - C ^ 2 - Complex.I * D ^ 2


def isingPrimalPrimitiveLaplacian (A B C D : Complex) : Real :=
  (((1 + Complex.I) / 2) *
    isingPrimitiveSquareCombination A B C D).im


def isingDualPrimitiveLaplacian (A B C D : Complex) : Real :=
  -isingPrimalPrimitiveLaplacian A B C D


noncomputable def isingPrimalProjectionDivergence
    (north east south west : Complex) : Real :=
  Complex.normSq (isingProj (-Complex.I) north) -
      Complex.normSq (isingProj (-1) north) +
    Complex.normSq (isingProj 1 east) -
      Complex.normSq (isingProj (-Complex.I) east) +
    Complex.normSq (isingProj Complex.I south) -
      Complex.normSq (isingProj 1 south) +
    Complex.normSq (isingProj (-1) west) -
      Complex.normSq (isingProj Complex.I west)


noncomputable def isingPrimalProjectionDivergenceWithoutSouth
    (north east west : Complex) : Real :=
  Complex.normSq (isingProj (-Complex.I) north) -
      Complex.normSq (isingProj (-1) north) +
    Complex.normSq (isingProj 1 east) -
      Complex.normSq (isingProj (-Complex.I) east) +
    Complex.normSq (isingProj (-1) west) -
      Complex.normSq (isingProj Complex.I west)


end
end StatMech.Universality
