/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part7


namespace StatMech.Universality

open Complex

open scoped ENNReal BigOperators


namespace HexWalk

def LegalTurns (w : HexWalk) : Prop := ∀ t ∈ w.turns, t = 1 ∨ t = -1


def IsSAW (w : HexWalk) : Prop := w.vertices.Nodup


def IsLegalSAW (w : HexWalk) : Prop := w.LegalTurns ∧ w.IsSAW


def trivialWalk (a : ℂ) (h : ℤ) : HexWalk := ⟨a, h, []⟩

end HexWalk
end StatMech.Universality
