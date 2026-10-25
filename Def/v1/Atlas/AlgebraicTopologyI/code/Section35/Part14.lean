/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Mathlib.Topology.Separation.Regular
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Category.TopCat.Opens
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Colimit.Module
import Mathlib.Order.Cofinal
import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section35.Part12
open Set


/-- Pointwise rel-to-abs map at a single neighborhood pair `i = (U, V)`:
$H^p(U, V) \to H^p(U)$, from the kernel inclusion. -/
noncomputable def CechCohomology.ptRelToAbs
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.relFamily X K L p i →+ CechCohomology.absKFamily X K L p i :=
  (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i))) p).hom.toAddMonoidHom

/-- Pointwise restriction map at `i = (U, V)`: $H^p(U) \to H^p(V)$, induced by
pullback along the inclusion $V \hookrightarrow U$. -/
noncomputable def CechCohomology.ptRestrict
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.absKFamily X K L p i →+ CechCohomology.absLFamily X K L p i :=
  (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion i)) p).hom.toAddMonoidHom


/-- The restriction-of-cochains map associated to a relative neighborhood pair
is an epimorphism in the category of cochain complexes of `ℤ`-modules. -/
noncomputable def CechCohomology.cochainSES
    {X : Type} [TopologicalSpace X] {K L : Set X}
    (i : CechCohomology.lesIndexType X K L) :
    (CategoryTheory.ShortComplex.mk
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i)))
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i))
      (CategoryTheory.Limits.kernel.condition _)).ShortExact := by
  letI : CategoryTheory.Abelian (CochainComplex (ModuleCat.{0} ℤ) ℕ) := inferInstance
  exact CategoryTheory.ShortComplex.ShortExact.mk
    (CategoryTheory.ShortComplex.exact_of_f_is_kernel _
      (CategoryTheory.Limits.kernelIsKernel _))

/-- Pointwise connecting homomorphism $H^p(V) \to H^{p+1}(U, V)$ associated to
`cochainSES i`. -/
noncomputable def CechCohomology.ptConnecting
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ)
    (i : CechCohomology.lesIndexType X K L) :
    CechCohomology.absLFamily X K L p i →+ CechCohomology.relFamily X K L (p + 1) i :=
  ((CechCohomology.cochainSES i).δ p (p + 1) rfl).hom.toAddMonoidHom


/-- Definitional identification of `CechCohomRel X K L p` with the direct limit
of `relFamily`. -/
noncomputable def CechCohomology.eqvRel
    (X : Type) [TopologicalSpace X] (K L : Set X) (p : ℕ) :
    CechCohomology.CechCohomRel X K L p ≃+
    AddCommGroup.DirectLimit (CechCohomology.relFamily X K L p)
      (CechCohomology.relBond X K L p) :=
  AddEquiv.refl _


