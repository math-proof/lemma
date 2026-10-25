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
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section36
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

namespace FullyRelativeCapProduct

variable (R : Type) [CommRing R]

/-- The continuous inclusion `A ↪ X` of a subset `A ⊆ X` as a morphism in `TopCat`,
given by the subtype valuation map. -/
def subtypeIncl (X : TopCat.{0}) (A : Set X) : TopCat.of A ⟶ X :=
  ⟨Subtype.val, continuous_subtype_val⟩

/-- The chain map `S_*(A; R) → S_*(X; R)` induced by the inclusion of a
subspace `A ⊆ X` into `X`. -/
def inclChainMap (X : TopCat.{0}) (A : Set X) :
    singChainCx R (TopCat.of A) ⟶ singChainCx R X :=
  ((singularChainComplexFunctor (ModuleCat.{0} R)).obj (ModuleCat.of R R)).map
    (subtypeIncl X A)

/-- The relative singular chain complex `S_*(X, A; R)`, defined as the cokernel
of the inclusion-induced chain map `S_*(A; R) → S_*(X; R)`. -/
def relSingChainCx (X : TopCat.{0}) (A : Set X) :
    ChainComplex (ModuleCat.{0} R) ℕ :=
  cokernel (inclChainMap R X A)

/-- The relative singular homology `H_n(X, A; R)`, defined as the `n`-th homology
of the relative singular chain complex. -/
def relSingularHomology (X : TopCat.{0}) (A : Set X) (n : ℕ) :
    ModuleCat.{0} R :=
  (relSingChainCx R X A).homology n

/-- The absolute singular homology `H_n(X; R)`, the `n`-th homology of the
singular chain complex. -/
def absSingularHomology (X : TopCat.{0}) (n : ℕ) : ModuleCat.{0} R :=
  (singChainCx R X).homology n

/-- The Čech cohomology `Ȟ^p(K; R)` of a subset `K ⊆ X`, obtained as the direct
limit of the singular cohomologies of open neighbourhoods of `K`. -/
def cechCohomology
    (X : TopCat.{0}) (K : Set X) (p : ℕ) : ModuleCat.{0} R :=
  CechCohomology.cechCohomology R K p

end FullyRelativeCapProduct
end
