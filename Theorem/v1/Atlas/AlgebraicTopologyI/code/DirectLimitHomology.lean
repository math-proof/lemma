/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/DirectLimitHomology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Homology.ShortComplex.Limits
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence

public section

/-- **Homology commutes with filtered colimits.**  In the abelian category
`AddCommGrpCat`, the degree-`n` homology functor on chain complexes
preserves filtered colimits.  This is the categorical content underlying
Corollary 23.13 (singular homology commutes with direct limits of spaces)
and Lemma 23 (homology of a direct limit of chain complexes is the direct
limit of the homologies). -/


namespace DirectLimitHomology

open CategoryTheory CategoryTheory.Limits HomologicalComplex

end DirectLimitHomology
