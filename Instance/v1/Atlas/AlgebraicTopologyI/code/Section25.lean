/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section25.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.Monoidal
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Topology.Category.TopCat.Monoidal
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import Theorem.v1.Atlas.AlgebraicTopologyI.code.EilenbergZilber
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section25
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
