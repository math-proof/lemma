/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part8
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

noncomputable def isingTorusSiteBoundaryAmplitude
    (i : Fin d) (beta : Real)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (F : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) : Real :=
  ∑ lower : ConfigSpace (IsingTorusStrictLower (k := k) i),
    isingTorusSiteHalfWeight i beta boundary lower * F lower

noncomputable def isingTorusSiteReflectionForm
    (i : Fin d) (beta : Real)
    (F G : ConfigSpace (IsingTorusStrictLower (k := k) i) → Real) : Real :=
  ∑ boundary : ConfigSpace (IsingTorusSitePlane (k := k) i),
    ∑ lower : ConfigSpace (IsingTorusStrictLower (k := k) i),
      ∑ upper : ConfigSpace (IsingTorusStrictLower (k := k) i),
        (isingTorusSiteHalfWeight i beta boundary lower * F lower) *
          (isingTorusSiteHalfWeight i beta boundary upper * G upper)

end StatMech.FrontierA
