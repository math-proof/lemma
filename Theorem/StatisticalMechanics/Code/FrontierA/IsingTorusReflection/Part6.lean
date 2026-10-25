/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusReflection.Part5
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

@[simp] theorem isingTorusSplitHalves_glueHalves
    (i : Fin d)
    (lower upper : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    isingTorusSplitHalves i (isingTorusGlueHalves i lower upper) =
      (lower, upper) := by
  apply Prod.ext
  · funext x
    simp [isingTorusSplitHalves, isingTorusGlueHalves, x.2]
  · funext x
    have hr : ¬ isingTorusInLowerHalf i
        (isingTorusReflectSite i x.1) :=
      fun h => (isingTorusReflectSite_not_lower_iff i x.1).mp h x.2
    simp [isingTorusSplitHalves, isingTorusGlueHalves, hr]

@[simp] theorem isingTorusGlueHalves_splitHalves
    (i : Fin d) (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    isingTorusGlueHalves i (isingTorusSplitHalves i sigma).1
      (isingTorusSplitHalves i sigma).2 = sigma := by
  funext x
  by_cases hx : isingTorusInLowerHalf i x
  · simp [isingTorusGlueHalves, isingTorusSplitHalves, hx]
  · simp [isingTorusGlueHalves, isingTorusSplitHalves, hx]


end StatMech.FrontierA
