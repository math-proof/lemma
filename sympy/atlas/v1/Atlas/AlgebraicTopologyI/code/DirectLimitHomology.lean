/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/DirectLimitHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.Algebra.Homology.ShortComplex.Abelian
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Homology.ShortComplex.Limits
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

namespace DirectLimitHomology

open CategoryTheory CategoryTheory.Limits HomologicalComplex

/-- **Homology commutes with filtered colimits.**  In the abelian category
`AddCommGrpCat`, the degree-`n` homology functor on chain complexes
preserves filtered colimits.  This is the categorical content underlying
Corollary 23.13 (singular homology commutes with direct limits of spaces)
and Lemma 23 (homology of a direct limit of chain complexes is the direct
limit of the homologies). -/
end DirectLimitHomology
