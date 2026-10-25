/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FKPositiveSubcriticalQ2Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.FiniteIsingFKBridge.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.SurfaceTensionConvexity
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.IsingFK.IsingBoxEncoding.Part4
import Theorem.StatisticalMechanics.Code.IsingFK.MagPercoIdBox.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.CurrentRep.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.FluxEdgeCopyBridge.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.FieldGhostDict.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneProps.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.SimonLiebFull.Part2
import Def.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part21
open Filter
open MeasureTheory
open scoped symmDiff
open scoped Topology


namespace StatMech

namespace Exact3D

@[simp] theorem boundaryGhostCoupling_some_some
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    (H : ℝ) (J : Sym2 V → ℝ) (x y : V) :
    boundaryGhostCoupling bdry H J s(some x, some y) = J s(x, y) := rfl

@[simp] theorem boundaryGhostCoupling_some_none
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    (H : ℝ) (J : Sym2 V → ℝ) (x : V) :
    boundaryGhostCoupling bdry H J s(some x, none) =
      if bdry x then H else 0 := rfl

@[simp] theorem boundaryGhostCoupling_none_some
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    (H : ℝ) (J : Sym2 V → ℝ) (x : V) :
    boundaryGhostCoupling bdry H J s(none, some x) =
      if bdry x then H else 0 := rfl

@[simp] theorem boundaryGhostCoupling_none_none
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    (H : ℝ) (J : Sym2 V → ℝ) :
    boundaryGhostCoupling bdry H J s(none, none) = 0 := rfl

@[simp] theorem boundaryGhostCoupling_some_none_of_boundary
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    {H : ℝ} (J : Sym2 V → ℝ) {x : V} (hx : bdry x) :
    boundaryGhostCoupling bdry H J s(some x, none) = H := by
  simp [hx]

@[simp] theorem boundaryGhostCoupling_some_none_of_not_boundary
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    {H : ℝ} (J : Sym2 V → ℝ) {x : V} (hx : ¬ bdry x) :
    boundaryGhostCoupling bdry H J s(some x, none) = 0 := by
  simp [hx]

@[simp] theorem boundaryGhostCoupling_none_some_of_boundary
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    {H : ℝ} (J : Sym2 V → ℝ) {x : V} (hx : bdry x) :
    boundaryGhostCoupling bdry H J s(none, some x) = H := by
  simp [hx]

@[simp] theorem boundaryGhostCoupling_none_some_of_not_boundary
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    {H : ℝ} (J : Sym2 V → ℝ) {x : V} (hx : ¬ bdry x) :
    boundaryGhostCoupling bdry H J s(none, some x) = 0 := by
  simp [hx]


theorem boundaryGhostCoupling_nonneg
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    {H : ℝ} {J : Sym2 V → ℝ} (hH : 0 ≤ H) (hJ : ∀ e, 0 ≤ J e) :
    ∀ e, 0 ≤ boundaryGhostCoupling bdry H J e := by
  intro e
  induction e with
  | h a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp
      · by_cases hy : bdry y <;> simp [hy, hH]
      · by_cases hx : bdry x <;> simp [hx, hH]
      · simpa using hJ s(x, y)


theorem boundaryGhostCoupling_zero_eq_ghostCoupling_zero
    {V : Type*} [DecidableEq V]
    (bdry : V → Prop) [DecidablePred bdry]
    (β : ℝ) :
    boundaryGhostCoupling bdry (0 : ℝ) (fun _ : Sym2 V => (1 : ℝ)) =
      Sharpness.FieldGhostDict.ghostCoupling (0 : ℝ) β (fun _ => 1) := by
  funext e
  induction e with
  | h a b =>
      rcases a with _ | x <;> rcases b with _ | y <;>
        simp [boundaryGhostCoupling, Sharpness.FieldGhostDict.ghostCoupling]


theorem boundaryGhostCoupling_mono_H
    {V : Type*} [DecidableEq V] (bdry : V → Prop) [DecidablePred bdry]
    {H₁ H₂ : ℝ} (hH : H₁ ≤ H₂) (J : Sym2 V → ℝ) :
    ∀ e, boundaryGhostCoupling bdry H₁ J e ≤
      boundaryGhostCoupling bdry H₂ J e := by
  intro e
  induction e with
  | h a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp
      · by_cases hy : bdry y <;> simp [hy, hH]
      · by_cases hx : bdry x <;> simp [hx, hH]
      · simp


end Exact3D
end StatMech
