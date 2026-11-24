module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.CupProductHelpers
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.RingTheory.Coalgebra.Basic
public import Mathlib.RingTheory.PrincipalIdealDomain
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Graded.External
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section26.Part3
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SingularCohomology

open scoped Simplicial

open Opposite SimplexCategory

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 3200000 in
/-- Build a singular `0`-cochain `C^0(X; N)` from a function `g : X → N`,
sending each singular `0`-simplex `σ₀` to the linear map `1 ↦ g(σ₀)`. -/
noncomputable def cochainOfFunc (X : TopCat.{0}) (N : ModuleCat.{0} ℤ)
    (g : X → N) : (singularCochainComplex ℤ X N).X 0 :=
  Sigma.desc (fun (σ₀ : Sing 0 X) =>
    ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ N (g (sing0EquivX X σ₀))))

end SingularCohomology
