/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryConnectivityTransfer.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectTorusRandomCluster.Part5
import Theorem.StatisticalMechanics.Code.Foundations.FiniteNonnegativeMatrixRate.Part2
import Theorem.StatisticalMechanics.Code.Lattice.EulerFaces2.Part2
import Def.StatisticalMechanics.Code.FrontierD.FKRectBoundaryConnectivityTransfer.Part16
open Finset Matrix Filter Topology


namespace StatMech.FrontierD

noncomputable section

attribute [local instance] Classical.propDecidable


@[simp] theorem fkRectStripLayerEmbed_initial {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerInitialRole, x) =
      Sum.inl (fkRectStripInitial n x) := by
  simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
    fkRectLayerOldRole]

@[simp] theorem fkRectStripLayerEmbed_old {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerOldRole, x) =
      Sum.inl (fkRectStripCurrent n x) := by
  simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
    fkRectLayerOldRole]

@[simp] theorem fkRectStripLayerEmbed_new {W : Nat} (n : Nat) (x : Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerNewRole, x) = Sum.inr x := by
  simp [fkRectStripLayerEmbed, fkRectLayerInitialRole,
    fkRectLayerOldRole, fkRectLayerNewRole]

@[simp] theorem fkRectStripLayerEmbed_input {W : Nat} (n : Nat)
    (u : Bool × Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerInputEmbed u) =
      Sum.inl (fkRectStripBoundary n u) := by
  cases u with
  | mk b x =>
      cases b <;> simp [fkRectLayerInputEmbed]

@[simp] theorem fkRectStripLayerEmbed_output {W : Nat} (n : Nat)
    (u : Bool × Fin W) :
    fkRectStripLayerEmbed n (fkRectLayerOutputEmbed u) =
      fkRectStripBoundary (n + 1) u := by
  cases u with
  | mk b x =>
      cases b <;> simp [fkRectLayerOutputEmbed, fkRectStripBoundary,
        fkRectStripInitial, fkRectStripCurrent]


end
end StatMech.FrontierD
