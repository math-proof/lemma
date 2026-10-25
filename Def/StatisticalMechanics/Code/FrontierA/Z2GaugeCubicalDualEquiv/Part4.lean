/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalDualEquiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualGeometry.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalDualEquiv.Part3
open scoped symmDiff
open Finset


namespace StatMech.FrontierA

noncomputable section

def cellFinsetAnchoredEquiv {a b c : Nat} :
    Finset (CubicalCell a b c) ≃
      AnchoredConfig (Option (CubicalCell a b c)) none where
  toFun S := ⟨fun q => match q with
    | none => false
    | some x => decide (x ∈ S), rfl⟩
  invFun s := Finset.univ.filter fun q => s.1 (some q) = true
  left_inv S := by
    ext q
    simp
  right_inv s := by
    apply Subtype.ext
    funext q
    cases q with
    | none => exact s.2.symm
    | some q =>
        cases h : s.1 (some q) <;> simp [h]


def finBackward {n : Nat} (k : Fin (n + 1)) : Option (Fin n) :=
  Fin.cases none some k


def finForward {n : Nat} (k : Fin (n + 1)) : Option (Fin n) :=
  Fin.lastCases none some k

end
end StatMech.FrontierA
