/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingInfraredBlockAverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingDyadicGreenRiemann.Part6
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusStationarity
open Finset
open scoped BigOperators ComplexConjugate


namespace StatMech.FrontierA

variable {Gamma : Type*} [Fintype Gamma] [AddCommGroup Gamma]


noncomputable def finiteTorusBlockDifferenceAverage
    (G : Gamma → Real) (B : Finset Gamma) : Real :=
  (1 / (B.card : Real) ^ 2) *
    ∑ a ∈ B, ∑ b ∈ B, G (b - a)


noncomputable def finiteTorusBlockCharacterWeight
    (B : Finset Gamma) (chi : AddChar Gamma Complex) : Real :=
  Complex.normSq (∑ a ∈ B, chi a) / (B.card : Real) ^ 2

end StatMech.FrontierA
