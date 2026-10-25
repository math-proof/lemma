/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.FrontierD.SixVertex.Part9
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexPerron.Part3
open Finset Matrix


namespace StatMech.FrontierD

def lowerSectorEmbedding {N n : ℕ} (f : Fin n ↪o Fin N) : Fin n ↪o Fin N := by
  let g : Fin n → Fin N := fun i =>
    ⟨max i.val ((f i).val - 1), by
      have hi : i.val ≤ (f i).val := fin_val_le_of_strictMono f f.strictMono i
      have : max i.val ((f i).val - 1) ≤ (f i).val := max_le hi (Nat.sub_le _ _)
      exact this.trans_lt (f i).prop⟩
  refine OrderEmbedding.ofStrictMono g ?_
  intro i j hij
  have hmono : (f i).val < (f j).val := by
    exact_mod_cast f.strictMono hij
  have hleft : i.val ≤ (f i).val := fin_val_le_of_strictMono f f.strictMono i
  by_cases heq : (f i).val = i.val
  · change max i.val ((f i).val - 1) < max j.val ((f j).val - 1)
    calc
      max i.val ((f i).val - 1) = i.val := by simp [heq]
      _ < j.val := hij
      _ ≤ max j.val ((f j).val - 1) := le_max_left _ _
  · have hi : i.val ≤ (f i).val - 1 := by omega
    change max i.val ((f i).val - 1) < max j.val ((f j).val - 1)
    rw [max_eq_right hi]
    calc
      (f i).val - 1 < (f i).val := by omega
      _ ≤ (f j).val - 1 := by omega
      _ ≤ max j.val ((f j).val - 1) := le_max_right _ _


noncomputable def sixVertexLowerSector {N n : ℕ} (x : SixVertexSector N n) :
    SixVertexSector N n :=
  Set.powersetCard.ofFinEmbEquiv (lowerSectorEmbedding (sixVertexSectorPosition x))

end StatMech.FrontierD
