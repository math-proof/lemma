module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section29
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section25
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section29.Part7
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section25.Part3
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Basis.Prod
public import Def.v1.Atlas.AlgebraicTopologyI.code.CohomologyKunneth
open CategoryTheory AlgebraicTopology Limits SingularCohomology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CohomologyKunneth.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped TensorProduct

namespace CohomologyKunneth

/-- Auxiliary statement of the bijectivity of the Kronecker pairing
`H^n(X; R) → Hom_R(H_n(X; R), R)` when `R` is a PID and every singular homology
module of `X` is finitely generated and free. This is the universal coefficient
isomorphism in this special case. -/
abbrev totalDualHomology (R : Type) [CommRing R] (X : TopCat.{0}) : Type :=
  DirectSum ℕ (fun n => (singularHomologyModule R X n : Type) →ₗ[R] R)

end CohomologyKunneth
end
