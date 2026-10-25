/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexParticleHole.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part9
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexParticleHole.Part3
open Finset Matrix


namespace StatMech.FrontierD

def sixVertexSectorComplement {N n : ℕ}
    (x : SixVertexSector N n) : SixVertexSector N (N - n) :=
  ⟨(x : Finset (Fin N))ᶜ, by simp [Finset.card_compl]⟩


def sixVertexSectorParticleHoleEquiv (N n : ℕ) (hn : n ≤ N) :
    SixVertexSector N n ≃ SixVertexSector N (N - n) where
  toFun := sixVertexSectorComplement
  invFun y := ⟨(y : Finset (Fin N))ᶜ, by
    have hy := y.prop
    change ((y : Finset (Fin N))ᶜ).card = n
    change (y : Finset (Fin N)).card = N - n at hy
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega⟩
  left_inv x := by
    apply Subtype.ext
    simp [sixVertexSectorComplement]
  right_inv y := by
    apply Subtype.ext
    simp [sixVertexSectorComplement]

end StatMech.FrontierD
