/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CohomologyKunneth.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section29
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section25
import Def.v1.Atlas.AlgebraicTopologyI.code.Section29.Part7
import Def.v1.Atlas.AlgebraicTopologyI.code.Section25.Part3
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.Basis.Prod
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.CohomologyKunneth.Part2
open CategoryTheory AlgebraicTopology Limits SingularCohomology


noncomputable section

open scoped TensorProduct

namespace CohomologyKunneth

/-- The bidegree-`(p, q)` component of an inverse to the homology Künneth map
in degree `n = p + q`: pick a splitting of the Künneth short exact sequence on
`X` and `Y` and project the resulting retraction onto the
`H_p(X; R) ⊗ H_q(Y; R)` summand. -/
def kunnethInvComponent
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0}) (p q : ℕ)
    (_hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type)) :
    (singularHomologyModule R (TopCat.of (↑X × ↑Y)) (p + q) : Type) →ₗ[R]
      TensorProduct R (singularHomologyModule R X p : Type)
        (singularHomologyModule R Y q : Type) :=
  let n := p + q
  let split := (KunnethTopological.kunnethShortExact_splitting R n X Y).some
  let retract := split.r
  let idx : { pq : ℕ × ℕ // pq.1 + pq.2 = n } := ⟨(p, q), rfl⟩
  let proj := Sigma.π (fun (pq : { pq : ℕ × ℕ // pq.1 + pq.2 = n }) =>
    MonoidalCategory.tensorObj (KunnethTopological.singularHomologyMod R pq.1.1 X)
      (KunnethTopological.singularHomologyMod R pq.1.2 Y)) idx
  (retract ≫ proj).hom

/-- Bidegree-`(p, q)` component of the left edge of the commuting diagram used
to prove bijectivity of the cohomology cross product: apply the Kronecker
pairings on each factor, distribute the tensor product through the dual, and
dualize the Künneth inverse component. -/
def componentDiagramLeftMap
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0}) (p q : ℕ)
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type)) :
    TensorProduct R (singularCohomologyFamily R X p)
      (singularCohomologyFamily R Y q) →ₗ[R]
      ((singularHomologyModule R (TopCat.of (↑X × ↑Y)) (p + q) : Type) →ₗ[R] R) :=

  ((kunnethInvComponent R X Y p q hfree).dualMap).comp

    ((TensorProduct.dualDistrib R
      (singularHomologyModule R X p : Type)
      (singularHomologyModule R Y q : Type)).comp

      (TensorProduct.map (kroneckerPairing R X p) (kroneckerPairing R Y q)))

/-- The total left edge of the comparison diagram: a linear map
`H^*(X; R) ⊗_R H^*(Y; R) → ⨁_n Hom_R(H_n(X × Y; R), R)` assembled from the
bidegree components `componentDiagramLeftMap`. -/
def diagramLeftMap
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    (totalSingularCohomology R X ⊗[R] totalSingularCohomology R Y) →ₗ[R]
      totalDualHomology R (TopCat.of (↑X × ↑Y)) :=


  (DirectSum.toModule R (ℕ × ℕ)
    (totalDualHomology R (TopCat.of (↑X × ↑Y)))
    (fun pq =>
      (DirectSum.lof R ℕ
        (fun n => (singularHomologyModule R (TopCat.of (↑X × ↑Y)) n : Type) →ₗ[R] R)
        (pq.1 + pq.2)).comp
        (componentDiagramLeftMap R X Y pq.1 pq.2 hfree))).comp
    (TensorProduct.directSum R R
      (singularCohomologyFamily R X)
      (singularCohomologyFamily R Y)).toLinearMap

/-- The total right edge of the comparison diagram: apply the Kronecker
pairing in each degree to convert `H^*(X × Y; R)` into the direct sum of duals
`⨁_n Hom_R(H_n(X × Y; R), R)`. -/
def diagramRightMap
    (R : Type) [CommRing R] [IsPrincipalIdealRing R]
    (X Y : TopCat.{0})
    (hfree : ∀ n, Module.Free R (singularHomologyModule R X n : Type))
    (hfg : ∀ n, Module.Finite R (singularHomologyModule R X n : Type)) :
    totalSingularCohomology R (TopCat.of (↑X × ↑Y)) →ₗ[R]
      totalDualHomology R (TopCat.of (↑X × ↑Y)) :=
  DirectSum.toModule R ℕ (totalDualHomology R (TopCat.of (↑X × ↑Y)))
    (fun n => (DirectSum.lof R ℕ
      (fun n => (singularHomologyModule R (TopCat.of (↑X × ↑Y)) n : Type) →ₗ[R] R) n).comp
      (kroneckerPairing R (TopCat.of (↑X × ↑Y)) n))

end CohomologyKunneth
end
