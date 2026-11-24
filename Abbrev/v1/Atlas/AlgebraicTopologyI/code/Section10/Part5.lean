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
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section10.Part2
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace BrouwerFixedPoint

open Metric Set Inner

/-- The functor `H_k(−; ℤ) : TopCat → AddCommGrpCat`, packaged for use in the Brouwer proof. -/
noncomputable abbrev homFunctorZ (k : ℕ) : TopCat.{0} ⥤ AddCommGrpCat :=
  (AlgebraicTopology.singularHomologyFunctor AddCommGrpCat k).obj (AddCommGrpCat.of ℤ)


end BrouwerFixedPoint
