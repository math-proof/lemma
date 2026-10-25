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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section24.Part2
open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace UniversalCoefficientTheorem

/-- The composition of the canonical map into cycles with `cyclesToHomologyTC` vanishes;
i.e. boundaries are killed. This is the relation needed to descend `cyclesToHomologyTC`
along the cokernel description of homology. -/
lemma toCycles_comp_cyclesToHomologyTC (R : Type*) [CommRing R] (M : ModuleCat R)
    (n : ℕ) (C : ChainComplex (ModuleCat R) ℕ) :
    ((tensoringRight (ModuleCat R)).obj M).map (C.toCycles (n + 2) (n + 1)) ≫
      cyclesToHomologyTC R M n C = 0 := by
  simp only [cyclesToHomologyTC, ← Category.assoc]
  rw [HomologicalComplex.comp_liftCycles]
  refine HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary
    (tensorComplex R C M) _ n (down_next_succ n) (𝟙 _) ?_
  rw [Category.id_comp]
  change ((tensoringRight (ModuleCat R)).obj M).map (C.toCycles (n + 2) (n + 1)) ≫
    ((tensoringRight (ModuleCat R)).obj M).map (C.iCycles (n + 1)) =
    ((tensoringRight (ModuleCat R)).obj M).map (C.d (n + 2) (n + 1))
  rw [← ((tensoringRight (ModuleCat R)).obj M).map_comp, HomologicalComplex.toCycles_i]

end UniversalCoefficientTheorem
end
