/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CupProductHelpers
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Graded.External
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section26
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct


noncomputable section

namespace SingularCohomology

/-- **Definition 26.5**. The $n$th singular cohomology
$H^n(X; G) = H^n(\operatorname{Hom}_R(S_*(X; R), G))$ of $X$ with coefficients in an
$R$-module $G$. -/
def singularCohomology (R : Type) [CommRing R]
    (X : TopCat.{0}) (G : ModuleCat.{0} R) (n : ℕ) :
    ModuleCat R :=
  ((((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X).linearYonedaObj R G).homology n

/-- The singular cochain complex $S^*(X; G) = \operatorname{Hom}_R(S_*(X; R), G)$, the
underlying cochain complex computing singular cohomology. -/
def singularCochainComplex (R : Type) [CommRing R]
    (X : TopCat.{0}) (G : ModuleCat.{0} R) : CochainComplex (ModuleCat.{0} R) ℕ :=
  (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).obj X).linearYonedaObj R G

/-- The restriction map of cochain complexes $S^*(X; G) \to S^*(A; G)$ induced by an inclusion
$A \hookrightarrow X$. -/
def restrictionCochainMap (R : Type) [CommRing R]
    (G : ModuleCat.{0} R) {X A : TopCat.{0}} (i : A ⟶ X) :
    singularCochainComplex R X G ⟶ singularCochainComplex R A G :=
  (HomologicalComplex.unopFunctor (ModuleCat.{0} R) (ComplexShape.down ℕ)).map
    (((((linearYoneda R (ModuleCat.{0} R)).obj G).rightOp.mapHomologicalComplex
      (ComplexShape.down ℕ)).map
      (((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
        (ModuleCat.of R R)).map i)).op)

/-- **Definition 26.8**. The relative singular cochain complex
$S^n(X, A; N) = \ker(S^n(X; N) \to S^n(A; N))$. -/
def relativeSingularCochainComplex (R : Type) [CommRing R]
    (G : ModuleCat.{0} R) {X A : TopCat.{0}} (i : A ⟶ X) :
    CochainComplex (ModuleCat.{0} R) ℕ :=
  haveI : HasKernels (CochainComplex (ModuleCat.{0} R) ℕ) := inferInstance
  kernel (restrictionCochainMap R G i)

/-- **Definition 26.8** (cohomology version). Relative singular cohomology
$H^n(X, A; N) = H^n(S^*(X, A; N))$. -/
def relativeSingularCohomology (R : Type) [CommRing R]
    (X A : TopCat.{0}) (i : A ⟶ X) (G : ModuleCat.{0} R) (n : ℕ) :
    ModuleCat R :=
  haveI : HasKernels (CochainComplex (ModuleCat.{0} R) ℕ) := inferInstance
  (kernel (restrictionCochainMap R G i)).homology n

end SingularCohomology
end
