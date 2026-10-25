/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusSiteReflection.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusSpinReflection.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingTorusSiteReflection.Part7
open Finset
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Ising

variable {d k : Nat}

theorem isingTorusSiteWeight_factor
    (i : Fin d) (beta : Real)
    (boundary : ConfigSpace (IsingTorusSitePlane (k := k) i))
    (lower upper : ConfigSpace (IsingTorusStrictLower (k := k) i)) :
    Real.exp (-(beta / 2) * isingTorusDirichlet
        (isingTorusSpinField (isingTorusSiteGlue i boundary lower upper))) =
      isingTorusSiteHalfWeight i beta boundary lower *
        isingTorusSiteHalfWeight i beta boundary upper := by
  unfold isingTorusSiteHalfWeight
  rw [← Real.exp_add]
  congr 1
  have h := isingTorusSiteGlue_dirichlet_midpoint
    i boundary lower upper
  calc
    -(beta / 2) * isingTorusDirichlet
        (isingTorusSpinField
          (isingTorusSiteGlue i boundary lower upper)) =
      -(beta / 4) * (2 * isingTorusDirichlet
        (isingTorusSpinField
          (isingTorusSiteGlue i boundary lower upper))) := by ring
    _ = -(beta / 4) *
        (isingTorusDirichlet
            (isingTorusSpinField
              (isingTorusSiteGlue i boundary lower lower)) +
          isingTorusDirichlet
            (isingTorusSpinField
              (isingTorusSiteGlue i boundary upper upper))) := by rw [h]
    _ = -(beta / 4) * isingTorusDirichlet
          (isingTorusSpinField
            (isingTorusSiteGlue i boundary lower lower)) +
        -(beta / 4) * isingTorusDirichlet
          (isingTorusSpinField
            (isingTorusSiteGlue i boundary upper upper)) := by ring


end StatMech.FrontierA
