module
public import Mathlib.AlgebraicTopology.SingularHomology.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Topology.Compactness.Compact
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Comma.Final
public import Mathlib.Topology.Separation.Hausdorff
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section37.Part2
open CategoryTheory
open CategoryTheory TopologicalSpace Limits


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace PoincareDuality

universe u

section OpenNhdsColimit

variable {α : Type u} [TopologicalSpace α]

namespace CombinedOpenNhds

variable {A : ℕ → Set α}

/-- **Lemma 37.2 (categorical core).** In a Hausdorff space, for any presheaf $F$ on the
opens of $\alpha$ and an antitone family of compacts $A_k$ with intersection $A$, the colimit
of $F$ over open neighbourhoods of $A$ is canonically isomorphic to the colimit of $F$
along the combined index built from the $A_k$. -/
noncomputable def cechCohomology_colimit_iso [T2Space α]
    {C : Type*} [Category C]
    (A : ℕ → Set α) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (F : (Opens α)ᵒᵖ ⥤ C)
    [HasColimit (OpenNhdsOfSet.inclusionFunctorOp ⋙ F : OpenNhdsOfSet (⋂ k, A k) ⥤ C)] :
    let G := (OpenNhdsOfSet.inclusionFunctorOp ⋙ F : OpenNhdsOfSet (⋂ k, A k) ⥤ C)
    letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
    letI : (toNhdsInter_monotone hA).functor.Final :=
      toNhdsInter_functor_final hA hcpt
    colimit ((toNhdsInter_monotone hA).functor ⋙ G) ≅ colimit G := by
  letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
  haveI : (toNhdsInter_monotone hA).functor.Final :=
    toNhdsInter_functor_final hA hcpt
  exact Functor.Final.colimitIso _ _

end CombinedOpenNhds

end OpenNhdsColimit

section CechCohomologySpecialization

variable {α : Type} [TopologicalSpace α]

namespace CombinedOpenNhds

variable {A : ℕ → Set α}

/-- `cechCohomology_colimit_iso` specialised to `C = ModuleCat.{0} R`, the variant used to
prove Lemma 37.2 in the Čech-cohomology setting. -/
noncomputable def cechCohomology_colimit_iso_cech [T2Space α]
    (R : Type) [CommRing R]
    (A : ℕ → Set α) (hA : Antitone A) (hcpt : ∀ k, IsCompact (A k))
    (F : (Opens α)ᵒᵖ ⥤ ModuleCat.{0} R)
    [HasColimit (OpenNhdsOfSet.inclusionFunctorOp ⋙ F :
      OpenNhdsOfSet (⋂ k, A k) ⥤ ModuleCat.{0} R)] :
    let G := (OpenNhdsOfSet.inclusionFunctorOp ⋙ F :
      OpenNhdsOfSet (⋂ k, A k) ⥤ ModuleCat.{0} R)
    letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA
    letI : (toNhdsInter_monotone hA).functor.Final :=
      toNhdsInter_functor_final hA hcpt
    colimit ((toNhdsInter_monotone hA).functor ⋙ G) ≅ colimit G :=
  cechCohomology_colimit_iso A hA hcpt F

end CombinedOpenNhds
end CechCohomologySpecialization
end PoincareDuality
