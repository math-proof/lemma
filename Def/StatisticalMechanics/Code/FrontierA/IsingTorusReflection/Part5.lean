/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusGaussianDomination.Part3
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingTorusReflection
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

def isingTorusGlueHalves (i : Fin d)
    (lower upper : ConfigSpace (IsingTorusLowerSite (k := k) i)) :
    ConfigSpace (IsingDyadicTorus d k) :=
  fun x => if hx : isingTorusInLowerHalf i x then lower ⟨x, hx⟩
    else upper ⟨isingTorusReflectSite i x,
      (isingTorusReflectSite_not_lower_iff i x).mpr hx⟩


def isingTorusSplitHalves (i : Fin d)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    ConfigSpace (IsingTorusLowerSite (k := k) i) ×
      ConfigSpace (IsingTorusLowerSite (k := k) i) :=
  (fun x => sigma x.1, fun x => sigma (isingTorusReflectSite i x.1))

end StatMech.FrontierA
