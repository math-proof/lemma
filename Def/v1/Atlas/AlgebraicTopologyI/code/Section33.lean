/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section33.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section33
open CategoryTheory AlgebraicTopology Limits


noncomputable section

namespace SingularCohomology

variable (R : Type) [CommRing R]

/-- The pushforward $f_* : H_p(X; R) \to H_p(Y; R)$ on singular homology
induced by a continuous map `f : X → Y`. -/
def homologyPushforward (X Y : TopCat.{0}) (f : X ⟶ Y) (p : ℕ) :
    singularHomologyModule R X p ⟶ singularHomologyModule R Y p :=
  ((singularHomologyFunctor (ModuleCat.{0} R) p).obj (ModuleCat.of R R)).map f

/-- The cochain-level pullback $f^\# : S^\bullet(Y; R) \to S^\bullet(X; R)$
dual to the chain pushforward induced by `f : X → Y`. -/
def cochainPullbackMap (X Y : TopCat.{0}) (f : X ⟶ Y) :
    (singularChainCx R Y).linearYonedaObj R (ModuleCat.of R R) ⟶
    (singularChainCx R X).linearYonedaObj R (ModuleCat.of R R) :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R (ModuleCat.{0} R)).obj (ModuleCat.of R R)).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map f)).op

/-- The pullback $f^* : H^p(Y; R) \to H^p(X; R)$ on singular cohomology induced
by a continuous map `f : X → Y`. -/
def cohomologyPullback (X Y : TopCat.{0}) (f : X ⟶ Y) (p : ℕ) :
    singularCohomologyR R Y p ⟶ singularCohomologyR R X p :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{0} R) (ComplexShape.up ℕ) p).map
    (cochainPullbackMap R X Y f)

end SingularCohomology
end
