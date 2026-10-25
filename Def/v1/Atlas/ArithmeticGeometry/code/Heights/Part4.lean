/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Heights.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.GaloisPlaceHelper
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.GaloisPlaceHelper
import Structure.v1.Atlas.ArithmeticGeometry.code.Heights.Part2


noncomputable section

open Height MvPolynomial

namespace AbsoluteHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Empty.Finite ι]

attribute [instance] TwoIsogenyData.instAddCommGroup

attribute [instance] TwoIsogenyData.instDescentTargetGroup

attribute [instance] TwoIsogenyData.instDescentTarget'Group

attribute [instance] TwoIsogenyData.descentMap_range_finite

attribute [instance] TwoIsogenyData.descentMap'_range_finite

def EllipticCurve.NeronTateHeight (h : W.toAffine.Point → ℝ)
    (_hWeil : IsWeilHeightOnCurve W h) (P : W.toAffine.Point) : ℝ :=
  canonicalHeight h P


end EllipticCurveCanonicalHeight

namespace TateTheorem

set_option linter.unusedSectionVars false in

def tateSeq {S : Type*} (φ : S → S) (h : S → ℝ) (r : ℝ) (x : S) (n : ℕ) : ℝ :=
  h (φ^[n] x) / r ^ n


noncomputable def mapCoords {K L : Type*} [CommRing K] [CommRing L]
    (σ : K →+* L) (n : ℕ) :
    (Fin (n + 1) → K) →ₛₗ[σ] (Fin (n + 1) → L) where
  toFun v i := σ (v i)
  map_add' x y := by ext i; simp [map_add]
  map_smul' c x := by ext i; simp [RingHom.map_mul]

def IsProjectiveMorphism {K : Type*} [CommRing K] {n m : ℕ} (d : ℕ)
    (φ : Fin (m + 1) → MvPolynomial (Fin (n + 1)) K) : Prop :=
  (∀ i, (φ i).IsHomogeneous d) ∧
  (∀ x : Fin (n + 1) → K, x ≠ 0 → ∃ i, MvPolynomial.eval x (φ i) ≠ 0)

end TateTheorem
end
