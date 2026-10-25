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
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section24
open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace UniversalCoefficientTheorem

/-- In the downward $\mathbb{N}$-indexed complex shape, the successor `n + 1` has
`next = n`. -/
lemma down_next_succ (n : ℕ) : (ComplexShape.down ℕ).next (n + 1) = n :=
  ComplexShape.next_eq' _ (ComplexShape.down_mk (n + 1) n (by omega))

/-- In the downward $\mathbb{N}$-indexed complex shape, the successor `n + 1` has
`prev = n + 2`. -/
lemma down_prev_succ (n : ℕ) : (ComplexShape.down ℕ).prev (n + 1) = n + 2 :=
  ComplexShape.prev_eq' _ (ComplexShape.down_mk (n + 2) (n + 1) (by omega))

/-- The image of the cycles inclusion $Z_{n+1}(C) \hookrightarrow C_{n+1}$ under the
functor $- \otimes M$ vanishes when followed by the differential of $C \otimes M$. Used
to lift the cycles into the homology of the tensor complex. -/
lemma iCycles_tensor_comp_d (R : Type*) [CommRing R] (M : ModuleCat R)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) ≫
      (tensorComplex R C M).d (n + 1) n = 0 := by
  change _ ≫ ((tensoringRight (ModuleCat R)).obj M).map (C.d (n + 1) n) = 0
  rw [← ((tensoringRight (ModuleCat R)).obj M).map_comp,
    HomologicalComplex.iCycles_d, Functor.map_zero]

end UniversalCoefficientTheorem
end
