/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.Additive
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.RingTheory.Flat.CategoryTheory
open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace UniversalCoefficientTheorem

/-- The chain complex obtained from $C_*$ by tensoring degreewise on the right with the
$R$-module $M$: $(C_* \otimes M)_n = C_n \otimes M$ with the induced differential. -/
def tensorComplex (R : Type*) [CommRing R] (C : ChainComplex (ModuleCat R) ℕ)
    (M : ModuleCat R) : ChainComplex (ModuleCat R) ℕ :=
  (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).obj C

/-- Functoriality of `tensorComplex` in the chain complex argument: a chain map
$\varphi : C \to D$ tensored with the identity on $M$. -/
def tensorComplexMap (R : Type*) [CommRing R] {C D : ChainComplex (ModuleCat R) ℕ}
    (φ : C ⟶ D) (M : ModuleCat R) : tensorComplex R C M ⟶ tensorComplex R D M :=
  (((tensoringRight (ModuleCat R)).obj M).mapHomologicalComplex (ComplexShape.down ℕ)).map φ

end UniversalCoefficientTheorem
end
