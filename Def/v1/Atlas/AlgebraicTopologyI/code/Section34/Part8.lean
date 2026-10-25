/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section34.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section31
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section31.Part7
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.Algebra.Colimit.Module
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Order.Directed
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.Sets.Opens
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Geometry.Manifold.ChartedSpace
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section34.Part2
open CategoryTheory AlgebraicTopology TopologicalSpace SingularCohomology


noncomputable section

namespace CapProduct

variable (R : Type) [CommRing R]

/-- **Relative singular homology** `H_n(Y, A; R)`, packaged as a
`ModuleCat R`.  Defined as the homology in degree `n` of the *cokernel*
chain complex `C_*(Y) / C_*(A)`, where the inclusion `A ↪ Y` induces a
chain map between singular-chain complexes.  This is the standard
"relative chain complex" construction. -/
noncomputable def relativeSingularHomologyModule
    (R : Type) [CommRing R] (Y : TopCat.{0}) (A : Set Y) (n : ℕ) : ModuleCat.{0} R :=
  let incl : TopCat.of A ⟶ Y := ⟨Subtype.val, continuous_subtype_val⟩
  let chainMap := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj
    (ModuleCat.of R R)).map incl
  (CategoryTheory.Limits.cokernel chainMap).homology n

/-- **Descent of the cap product to relative singular homology.**  The
chain-level cap product `C^p(Y) ⊗ C_{p+q}(Y) → C_q(Y)` descends to a map
on relative homology
`H^p(Y; R) ⊗ H_{p+q}(Y, A) → H_q(Y, A)` because chains supported on `A`
are sent to chains supported on `A`.  This is the linear map of the
relative cap product in singular homology. -/
def relativePushforwardMap
    (R : Type) [CommRing R] {Y Z : TopCat.{0}} (f : Y ⟶ Z)
    (A : Set Y) (B : Set Z) (n : ℕ) :
    (relativeSingularHomologyModule R Y A n : Type) →ₗ[R]
    (relativeSingularHomologyModule R Z B n : Type) := by
  classical
  by_cases hf : Set.MapsTo f A B
  · let f_A : TopCat.of A ⟶ TopCat.of B :=
      ⟨fun a => ⟨f a.val, hf a.property⟩, by fun_prop⟩
    let SCF := ((singularChainComplexFunctor.{0} (ModuleCat.{0} R)).obj (ModuleCat.of R R))
    have comm : SCF.map (show TopCat.of A ⟶ Y from ⟨Subtype.val, continuous_subtype_val⟩) ≫
        SCF.map f =
        SCF.map f_A ≫
        SCF.map (show TopCat.of B ⟶ Z from ⟨Subtype.val, continuous_subtype_val⟩) := by
      rw [← Functor.map_comp, ← Functor.map_comp]
      congr 1
    exact (HomologicalComplex.homologyMap
      (CategoryTheory.Limits.cokernel.map _ _ (SCF.map f_A) (SCF.map f) comm) n).hom
  · exact 0


/-- **Excision at the chain level (quasi-isomorphism).**  For a closed
`K ⊂ X` and open neighborhoods `V ⊆ U` of `K`, the inclusion `V ↪ U`
induces a chain map of relative singular chain complexes
`C_*(V, V \ K) → C_*(U, U \ K)` which is a quasi-isomorphism in each
degree.  This is Mathlib's formulation of the classical excision theorem
at the level of `ModuleCat`-valued cokernels. -/
def backFace (p q : ℕ) : (⦋q⦌ : SimplexCategory) ⟶ ⦋p + q⦌ :=
  SimplexCategory.mkHom ⟨fun j => ⟨j.val + p, by omega⟩,
    fun a b (h : a ≤ b) => show a.val + p ≤ b.val + p by omega⟩

end CapProduct
end
