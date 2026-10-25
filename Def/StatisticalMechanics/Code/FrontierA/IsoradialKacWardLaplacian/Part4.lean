/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialKacWardLaplacian.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialCellularRibbonDuality.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsoradialKacWardLaplacian.Part2


namespace StatMech.FrontierA

open Matrix Finset

open scoped BigOperators

variable {V E D : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]


noncomputable def finiteCRSFWitnessTerm
    (conductance transport : V -> V -> Complex)
    (X : finiteCRSFWitness V) : Complex :=
  Equiv.Perm.sign X.1 •
    ((∏ v : laplacianPermutationFixedPoint X.1,
        conductance v (X.2 v)) *
      ∏ v ∈ (Finset.univ.filter fun v => X.1 v ≠ v),
        -conductance (X.1 v) v * transport (X.1 v) v)


end StatMech.FrontierA
