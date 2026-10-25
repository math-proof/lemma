/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousFiniteVolumeRelabel.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSInhomogeneous.Part11
import Theorem.StatisticalMechanics.Code.FK.AdditiveGluing.Part9
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel
open scoped BigOperators
open Finset


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Sharpness

variable {V W : Type*} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]


section Isolated

variable {X Y : Type*} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y]

noncomputable def sym2FinsetInl (E : Finset (Sym2 X)) :
    Finset (Sym2 (X ⊕ Y)) :=
  E.image (Sym2.map Sum.inl)

end Isolated
end StatMech.FrontierB
