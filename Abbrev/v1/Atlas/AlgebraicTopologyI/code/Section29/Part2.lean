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
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section29.Part3
open DirectSum GradedMonoid

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI


noncomputable section

namespace CupProduct

section SphereCupProduct

open CategoryTheory AlgebraicTopology Limits

variable (R : Type) [CommRing R]

/-- The singular cochain complex $C^*(X; G) = \mathrm{Hom}_R(C_*(X; R), G)$ of a
topological space $X$ with coefficients in an $R$-module $G$, as an object of
`CochainComplex (ModuleCat R) ℕ`. -/
noncomputable abbrev singCochains (G : ModuleCat.{0} R) (X : TopCat.{0}) :
    CochainComplex (ModuleCat R) ℕ :=
  (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X).linearYonedaObj R G

/-- The $n$-th singular cohomology $H^n(X; G)$ as an $R$-module, defined as the
homology of the cochain complex `singCochains R G X` in degree $n$. -/
noncomputable abbrev singCohom (G : ModuleCat.{0} R) (X : TopCat.{0}) (n : ℕ) :
    ModuleCat R :=
  (singCochains R G X).homology n

end SphereCupProduct
end CupProduct
end
