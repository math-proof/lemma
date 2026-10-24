/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.NormalOrderCoeff
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.NormalOrderCoeff
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.WalkCountOps
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.WalkCountOps

noncomputable section

open scoped Classical

open WalkCountFormula NormalOrderCoeff Finset

namespace WalkCountBridge

def toQ : (YoungDiagram →₀ ℤ) → (YoungDiagram →₀ ℚ) :=
  Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero

@[simp] theorem toQ_apply (f : YoungDiagram →₀ ℤ) (a : YoungDiagram) :
    (toQ f) a = ↑(f a) := by
  show Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero f a = ↑(f a)
  rw [Finsupp.mapRange_apply]

@[simp] theorem toQ_single (a : YoungDiagram) (c : ℤ) :
    toQ (Finsupp.single a c) = Finsupp.single a (↑c : ℚ) := by
  show Finsupp.mapRange (Int.cast : ℤ → ℚ) Int.cast_zero (Finsupp.single a c) = _
  rw [Finsupp.mapRange_single]

def liftU_Q : (YoungDiagram →₀ ℚ) →ₗ[ℚ] (YoungDiagram →₀ ℚ) :=
  Finsupp.lsum ℚ fun μ => LinearMap.id.smulRight (toQ (YoungDiagram.raisingOp μ))

def liftD_Q : (YoungDiagram →₀ ℚ) →ₗ[ℚ] (YoungDiagram →₀ ℚ) :=
  Finsupp.lsum ℚ fun μ => LinearMap.id.smulRight (toQ (YoungDiagram.loweringOp μ))

def emptyBasis_Q : YoungDiagram →₀ ℚ := Finsupp.single ⊥ 1

@[simp] theorem liftU_Q_single (a : YoungDiagram) (c : ℚ) :
    liftU_Q (Finsupp.single a c) = c • toQ (YoungDiagram.raisingOp a) := by simp [liftU_Q]

@[simp] theorem liftD_Q_single (a : YoungDiagram) (c : ℚ) :
    liftD_Q (Finsupp.single a c) = c • toQ (YoungDiagram.loweringOp a) := by simp [liftD_Q]
