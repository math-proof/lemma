/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


def sctBoxOrigin (d n : ℕ) : sctBox d n :=
  ⟨fun _ => 0, by intro i; simp⟩


def sctTranslatedBox (d n : ℕ) (y : Site d) : Set (Site d) :=
  (fun z : Site d => z - y) '' box d n


noncomputable def sctTranslateEquiv (d n : ℕ) (y : Site d) :
    sctBox d n ≃ {z : Site d // z ∈ sctTranslatedBox d n y} where
  toFun z := ⟨z.1 - y, ⟨z.1, z.2, rfl⟩⟩
  invFun w := ⟨w.1 + y, by
    rcases w.2 with ⟨z, hz, hzy⟩
    have hw : w.1 + y = z := by
      rw [← hzy]
      funext i
      dsimp
      ring
    rwa [hw]⟩
  left_inv z := by ext i; simp
  right_inv w := by ext i; simp


def sctTranslatedBoxGraph (d n : ℕ) (y : Site d) :
    SimpleGraph {z : Site d // z ∈ sctTranslatedBox d n y} :=
  (hypercubicLattice d).induce (sctTranslatedBox d n y)

end Sharpness
end StatMech
