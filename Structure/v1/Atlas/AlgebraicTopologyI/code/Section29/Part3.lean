/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
public import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section27
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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section29.Part5
open DirectSum GradedMonoid

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI


public noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

attribute [instance] instRingCupProductAlgebra


attribute [instance] instAlgebraCupProductAlgebra

/-- The *Koszul tensor algebra* $H^*(X; R) \otimes_R H^*(X; R)$, wrapping the
$R$-tensor product of two cohomology rings. The cohomology cross product will be
defined as a ring homomorphism out of this algebra. -/
structure KoszulTensorAlgebra (X Y : TopCat.{0}) : Type where
  toTensorProduct : TensorProduct R (CupProductAlgebra R X) (CupProductAlgebra R Y)


end SingularCohomology
end
