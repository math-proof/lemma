/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/DModuleApplications.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Algebra.Lie.Basic
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Irreducible


noncomputable section

structure SmoothVarietyWithGroupAction where
  X : Type*
  K : Type*
  [grpK : Group K]
  [topK : TopologicalSpace K]
  [connK : ConnectedSpace K]
  [actKX : MulAction K X]
  DX : Type*
  [ringDX : Ring DX]
  [algebraDX : Algebra ℂ DX]
  [actKDX : MulAction K DX]
  orbits : Set (Set X)
  orbit_is_orbit : ∀ O ∈ orbits, O.Nonempty ∧ (∀ x ∈ O, ∀ k : K, k • x ∈ O)
  orbits_cover : ∀ x : X, ∃ O ∈ orbits, x ∈ O
  orbits_disjoint : ∀ O₁ ∈ orbits, ∀ O₂ ∈ orbits, O₁ ≠ O₂ → Disjoint O₁ O₂
  orbits_finite : orbits.Finite

end
