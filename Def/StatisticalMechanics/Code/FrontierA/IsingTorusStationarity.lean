/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusStationarity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingInfraredSpatial
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}


noncomputable def isingTorusTwoPoint (beta : Real)
    (x y : IsingDyadicTorus d k) : Real :=
  (∑ sigma : ConfigSpace (IsingDyadicTorus d k),
      Real.exp (-(beta / 2) *
        isingTorusDirichlet (isingTorusSpinField sigma)) *
      isingTorusSpinField sigma x * isingTorusSpinField sigma y) /
    isingTorusShiftedPartition (d := d) (k := k) beta 0

end StatMech.FrontierA
