/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section29.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section27
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section27
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Algebra
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Algebra.Ring.TransferInstance
import Mathlib.Algebra.Algebra.TransferInstance
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Topology.Category.TopCat.Sphere
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.DirectSum.Basis
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section29.Part2
open DirectSum GradedMonoid

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI


noncomputable section

namespace CupProduct

section SphereCupProduct

open CategoryTheory AlgebraicTopology Limits

variable (R : Type) [CommRing R]

/-- Contravariant action of a continuous map $f : X \to Y$ on singular cochains:
the pullback $f^* : C^*(Y; G) \to C^*(X; G)$ defined by precomposition with the
induced chain map on $C_*(-; R)$. -/
noncomputable def pullbackCochainMap (G : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : X ⟶ Y) :
    singCochains R G Y ⟶ singCochains R G X :=
  let chainMap := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).map f
  let mapHC := (((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
    (ComplexShape.down ℕ)).map chainMap
  (HomologicalComplex.unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map mapHC.op

/-- The induced map $f^* : H^n(Y; G) \to H^n(X; G)$ on singular cohomology,
obtained from `pullbackCochainMap` by passing to homology in degree $n$. -/
noncomputable def cohomPullback (G : ModuleCat.{0} R) {X Y : TopCat.{0}} (f : X ⟶ Y) (n : ℕ) :
    singCohom R G Y n ⟶ singCohom R G X n :=
  HomologicalComplex.homologyMap (pullbackCochainMap R G f) n

end SphereCupProduct
end CupProduct
end
