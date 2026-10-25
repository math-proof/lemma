/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopRectangularSpectralBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopRectangularEmbedding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.KWRectangleWeighted.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusCycleTopology.Part2
import Def.StatisticalMechanics.Code.Onsager.SignedLoopRectangularSpectralBridge.Part2
open Finset SimpleGraph


namespace StatMech.Onsager

open StatMech.FrontierA

noncomputable section

@[simp] theorem ons_rectDualVertexSlot_fst_val {M N : Nat}
    (vertex : ons_RectDualVertex M N) :
    (ons_rectDualVertexSlot vertex).1.val = vertex.1.val := by
  simp [ons_rectDualVertexSlot, ZMod.val_natCast,
    Nat.mod_eq_of_lt vertex.1.isLt]

@[simp] theorem ons_rectDualVertexSlot_snd_val {M N : Nat}
    (vertex : ons_RectDualVertex M N) :
    (ons_rectDualVertexSlot vertex).2.val = vertex.2.val := by
  simp [ons_rectDualVertexSlot, ZMod.val_natCast,
    Nat.mod_eq_of_lt vertex.2.isLt]

theorem ons_rectDualVertexSlot_injective {M N : Nat} :
    Function.Injective
      (ons_rectDualVertexSlot : ons_RectDualVertex M N → ons_RectVertex M N) := by
  intro u v h
  apply Prod.ext <;> apply Fin.ext
  · have hx := congrArg (fun p : ons_RectVertex M N ↦ p.1.val) h
    simpa using hx
  · have hy := congrArg (fun p : ons_RectVertex M N ↦ p.2.val) h
    simpa using hy


end
end StatMech.Onsager
