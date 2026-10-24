/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountOps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.HasseWalks
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.HasseWalks
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungTableaux
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.YoungTableaux
import Mathlib.LinearAlgebra.Finsupp.LSum

noncomputable section

open scoped Classical

namespace WalkCountFormula

def liftU : (YoungDiagram →₀ ℤ) →ₗ[ℤ] (YoungDiagram →₀ ℤ) :=
  Finsupp.lsum ℤ (fun μ => LinearMap.id.smulRight (YoungDiagram.raisingOp μ))

def liftD : (YoungDiagram →₀ ℤ) →ₗ[ℤ] (YoungDiagram →₀ ℤ) :=
  Finsupp.lsum ℤ (fun μ => LinearMap.id.smulRight (YoungDiagram.loweringOp μ))

def iterU (n : ℕ) : (YoungDiagram →₀ ℤ) →ₗ[ℤ] (YoungDiagram →₀ ℤ) :=
  liftU ^ n

def emptyBasis : YoungDiagram →₀ ℤ := Finsupp.single ⊥ 1
