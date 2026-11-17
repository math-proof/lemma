/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.GroupTheory.FreeAbelianGroup
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Topology.Category.TopCat.Monoidal
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section25

@[expose] public section

open CategoryTheory MonoidalCategory Limits


noncomputable section

namespace TensorChainComplex

variable (R : Type) [CommRing R]

variable [IsPrincipalIdealRing R]

set_option linter.unusedSectionVars false in

/-- The category $\mathrm{ModuleCat}\,R$ of $R$-modules has projective resolutions; an
instance reused throughout the Tor / UCT / Künneth development. -/
instance moduleCat_hasProjectiveResolutions (R : Type) [Ring R] :
    HasProjectiveResolutions (ModuleCat.{0} R) := inferInstance

end TensorChainComplex
end
