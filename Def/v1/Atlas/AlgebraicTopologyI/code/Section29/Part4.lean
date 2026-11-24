module
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section27
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
public import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section27
public import Mathlib.Algebra.DirectSum.Ring
public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Algebra.Ring.TransferInstance
public import Mathlib.Algebra.Algebra.TransferInstance
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.LinearAlgebra.DirectSum.Basis
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section29
open DirectSum GradedMonoid
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

set_option maxHeartbeats 6400000 in
/-- The unit $1 \in H^0(X; R)$ of the cohomology ring, obtained as the
cohomology class of the augmentation cocycle $\varepsilon$. -/
noncomputable def cohomologyUnit
    (R : Type) [CommRing R] (X : TopCat.{0}) :
    singularCohomologyFamily R X 0 :=
  let K := singularCochainComplex R X (ModuleCat.of R R)
  let cycleElt : ↑((forget₂ (ModuleCat.{0} R) Ab).obj (K.cycles 0)) :=
    HomologicalComplex.cyclesMk K (augmentationCocycle R X) 1
      (CochainComplex.next ℕ 0)
      (by
        change (K.d 0 1).hom (augmentationCocycle R X) = 0
        simp only [K, singularCochainComplex, ChainComplex.linearYonedaObj_d]
        exact augmentationCocycle_coboundary_zero R X)
  (ConcreteCategory.hom ((forget₂ (ModuleCat.{0} R) Ab).map
    (CochainComplex.isoHomologyπ₀ K).hom)) cycleElt

end SingularCohomology
end
