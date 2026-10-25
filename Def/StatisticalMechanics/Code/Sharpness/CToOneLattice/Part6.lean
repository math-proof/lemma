/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Instance.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part5
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


noncomputable def sctTranslatedInDoubleEquiv (d n : ℕ) (y : sctBox d n) :
    {z : Site d // z ∈ sctTranslatedBox d n y.1} ≃
      {z : sctBox d (2 * n) // sctTranslatedInDouble d n y z} where
  toFun z := ⟨⟨z.1, sct_translate_box_subset_double y.2 z.2⟩, z.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv z := by ext i; rfl
  right_inv z := by ext i; rfl


end Sharpness
end StatMech
