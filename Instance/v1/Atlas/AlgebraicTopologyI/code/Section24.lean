/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section24.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section24

@[expose] public section

open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace UniversalCoefficientTheorem

/-- Tensoring on the right with a fixed module $M$ preserves colimits; obtained by
transporting along the symmetry isomorphism with `tensorLeft M`. -/
instance tensorRight_preservesColimits (R : Type*) [CommRing R] (M : ModuleCat R) :
    PreservesColimits ((tensoringRight (ModuleCat R)).obj M) := by
  change PreservesColimits (tensorRight M)
  exact preservesColimits_of_natIso
    (NatIso.ofComponents (fun X => (_root_.CategoryTheory.BraidedCategory.braiding M X))
      (fun {X Y} f => _root_.CategoryTheory.BraidedCategory.braiding_naturality_right M f) :
      tensorLeft M ≅ tensorRight M)

end UniversalCoefficientTheorem
end
