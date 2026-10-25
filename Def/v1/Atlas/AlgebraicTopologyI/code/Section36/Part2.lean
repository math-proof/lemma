/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Algebra.Group.Subgroup.Ker
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section36
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The inclusion `V ↪ U` of opens `V ≤ U` as a morphism in `TopCat`. -/
def opensInclusion {X : TopCat.{0}} (U V : TopologicalSpace.Opens X) (h : V ≤ U) :
    TopCat.of ↑V.1 ⟶ TopCat.of ↑U.1 :=
  ⟨fun x => ⟨x.1, h x.2⟩, continuous_inclusion h⟩

/-- The relative singular cohomology `H^p(U, V; R)` of an `OpenNbhdPair (U, V)`,
constructed as the `p`-th cohomology of the kernel of the cochain restriction
`S^*(U; R) → S^*(V; R)`. -/
def relCohomOfPair {X : TopCat.{0}} {K L : Set X}
    (pair : OpenNbhdPair K L) (p : ℕ) : ModuleCat.{0} R := by
  classical
  let G := ModuleCat.of R R
  let restrictMap :=
    (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
      (((((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
        (ComplexShape.down ℕ)).map
        (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj G).map
          (opensInclusion pair.U pair.V pair.hVU))).op)
  exact (kernel restrictMap).homology p

/-- The underlying type of `relCohomOfPair`, exposed as a `Type` to serve as
the type-theoretic family for the direct-limit construction of relative
Čech cohomology. -/
def relCechFamily {X : TopCat.{0}} {K L : Set X}
    (p : ℕ) (pair : OpenNbhdPair K L) : Type :=
  (relCohomOfPair R pair p : Type _)

end FullyRelativeCapProduct
end
