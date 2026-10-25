/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part7
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

noncomputable def isingTorusSiteHalfWeight
    (i : Fin d) (beta : Real)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower : ConfigSpace (IsingTorusStrictLower (k := k) i)) : Real :=
  Real.exp (-(beta / 4) * isingTorusDirichlet
    (isingTorusSpinField (isingTorusSiteGlue i boundary lower lower)))

end StatMech.FrontierA
