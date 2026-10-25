/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Abbrev.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

def isingTorusSiteGlue (i : Fin d)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    ConfigSpace (IsingDyadicTorus d k) :=
  fun x => if hp : isingTorusOnSitePlane i x then boundary ⟨x, hp⟩
    else if hl : isingTorusInStrictLower i x then lower ⟨x, hl⟩
    else upper ⟨isingTorusSiteReflect i x,
      isingTorusSiteReflect_strictLower_of_upper i hp hl⟩


def isingTorusSiteSplit (i : Fin d)
    (sigma : ConfigSpace (IsingDyadicTorus d k)) :
    ConfigSpace (IsingTorusSitePlane (k := k) i) ×
      (ConfigSpace (IsingTorusStrictLower (k := k) i) ×
        ConfigSpace (IsingTorusStrictLower (k := k) i)) :=
  (fun x => sigma x.1,
    (fun x => sigma x.1, fun x => sigma (isingTorusSiteReflect i x.1)))

end StatMech.FrontierA
