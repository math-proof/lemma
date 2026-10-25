/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusAxisMonotonicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part10
open Finset Set


namespace StatMech.FrontierA

open StatMech.Ising StatMech.Sharpness

variable {d k : Nat}

noncomputable def isingTorusAxisCorrelation
    (i : Fin d) (beta : Real) (n : Nat) : Real :=
  isingTorusTwoPoint (k := k) beta 0 (isingTorusCoordinateShift i n)

end StatMech.FrontierA
