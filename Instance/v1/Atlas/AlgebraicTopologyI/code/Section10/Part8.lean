module
public import Mathlib
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part13
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SphereHomology

open AlgebraicTopology

/-- Auxiliary form of `sphere_homology_top`: the top homology of `S^n` is `ℤ`, expressed in
terms of the `singularChainZF` complex. -/
noncomputable instance suspSingularChainZ_preserves_mono :
    ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ) :
      TopCat.{0} ⥤ ChainComplex AddCommGrpCat ℕ).PreservesMonomorphisms :=
  singularChainZ_preserves_mono

end SphereHomology
