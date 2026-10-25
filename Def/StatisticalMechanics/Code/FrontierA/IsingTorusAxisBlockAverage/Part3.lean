/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisBlockAverage.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusAxisMonotonicity
import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredBlockAverage
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusAxisBlockAverage.Part3
open Finset Set
open scoped BigOperators


namespace StatMech.FrontierA

variable {Gamma : Type*} [AddCommGroup Gamma]


variable {d k : Nat}


noncomputable def isingTorusSparseAxisBlock
    (i : Fin d) (spacing count : Nat) :
    Finset (IsingDyadicTorus d k) :=
  (Finset.range count).image fun j =>
    isingTorusCoordinateShift i (j * spacing)

end StatMech.FrontierA
