/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReflectedMatchingCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterMatchingCutCurrent.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Structure.StatisticalMechanics.Code.Ising.LebowitzPfisterReflectedMatchingCut
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

noncomputable section

variable {W I : Type*} [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I]


def lpReflectSource
    {G : SimpleGraph W} {J : Sym2 W -> Real}
    {left right : I -> W} {g0 g1 : W}
    (R : LPReflectedMatchingCut G J left right g0 g1)
    (S : Finset W) : Finset W :=
  S.map R.reflect.toEmbedding

end
end StatMech.Ising
