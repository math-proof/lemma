/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/InteriorReaches.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.ChordCut.Part5


namespace StatMech.Onsager.InteriorReaches

open StatMech.Onsager.ChordCut

open scoped BigOperators


def BoundedRight (D : BoxData) (S : Set Pt) : Prop :=
  ∀ p : Pt, p ∈ S → p.1 ≤ D.x1


def SeparatedBy (D : BoxData) (S : Set Pt) : Prop :=
  ∀ p : Pt, p ∉ D.B → (p.1 + 1, p.2) ∉ D.B → (p ∈ S ↔ (p.1 + 1, p.2) ∈ S)


def BoundaryCoversTransitions (D : BoxData) (S : Set Pt) : Prop :=
  ∀ p : Pt, ¬ (p ∈ S ↔ (p.1 + 1, p.2) ∈ S) → (p ∈ D.B ∨ (p.1 + 1, p.2) ∈ D.B)


end StatMech.Onsager.InteriorReaches
