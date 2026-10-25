/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenHomogeneity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Theorem.StatisticalMechanics.Code.Ising.IsingPlusTIFromPlacement.Part11
import Theorem.StatisticalMechanics.Code.FrontierB.FreeEvenHomogeneity
open MeasureTheory Filter Topology
open scoped BigOperators


namespace StatMech.FrontierB

open Ising Lattice Sharpness


noncomputable def freeDomainInclusionEquiv {d : Nat}
    {K L : Finset (Site d)} (hKL : K ⊆ L) :
    freeDomainVertices K ≃
      {z : freeDomainVertices L // z.1 ∈ K} where
  toFun x := ⟨⟨x.1, hKL x.2⟩, x.2⟩
  invFun z := ⟨z.1.1, z.2⟩
  left_inv x := by ext; rfl
  right_inv z := by ext; rfl

end StatMech.FrontierB
