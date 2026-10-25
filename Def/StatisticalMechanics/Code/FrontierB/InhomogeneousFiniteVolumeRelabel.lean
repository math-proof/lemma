/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
open scoped BigOperators
open Finset


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Sharpness

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]


noncomputable def sym2FinsetImage (sigma : V ≃ W)
    (E : Finset (Sym2 V)) : Finset (Sym2 W) :=
  E.image (Sym2.map sigma)

end StatMech.FrontierB
