/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/CotangentBundleBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.ManifoldDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.ManifoldDFS
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import sympy.atlas.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped Manifold ContDiff
open DifferentialFormSpace


/-- The cotangent bundle $T^*M$ as the disjoint union $\bigsqcup_{x \in M} T^*_x M$ of cotangent spaces. -/
def CotangentBundle
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H]
    (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
    [ChartedSpace H M] : Type _ :=
  Σ (x : M), (TangentSpace I x →ₗ[ℝ] ℝ)

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M]
variable [ChartedSpace H M]

/-- The bundle projection $\pi : T^*M \to M$, $(x, \xi) \mapsto x$. -/
def proj (p : CotangentBundle I M) : M := p.1

/-- Builds a cotangent vector at $x \in M$ from a covector $\xi \in T^*_x M$. -/
def mk (x : M) (ξ : TangentSpace I x →ₗ[ℝ] ℝ) : CotangentBundle I M := ⟨x, ξ⟩

/-- Projection of a built cotangent vector returns its basepoint. -/
@[simp] theorem proj_mk (x : M) (ξ : TangentSpace I x →ₗ[ℝ] ℝ) :
    proj I M (mk I M x ξ) = x := rfl

end CotangentBundle


universe u

section CotangentBundleManifold

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type u} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- The natural topology on $T^*M$ making the projection continuous (axiomatized). -/
end CotangentBundleManifold


section CotangentBundleDFSTypes

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type u} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- The model-with-corners for $T^*M$, namely $I \times \mathrm{id}_E$. -/
noncomputable abbrev cotangentBundleModel :
    ModelWithCorners ℝ (E × E) (ModelProd H E) :=
  I.prod (modelWithCornersSelf ℝ E)

/-- The space of differential $p$-forms on the cotangent bundle $T^*M$. -/
noncomputable abbrev CotangentBundleΩ (p : ℕ) : Type _ :=
  ManifoldΩ (cotangentBundleModel I) (CotangentBundle I M) p

/-- The space of vector fields on the cotangent bundle $T^*M$. -/
noncomputable abbrev CotangentBundleVF : Type _ :=
  ManifoldVF (cotangentBundleModel I) (CotangentBundle I M)

/-- The `DifferentialFormSpace` structure on $T^*M$, induced from its manifold structure. -/
@[reducible]
noncomputable def cotangentBundleDFSInst :
    DifferentialFormSpace (CotangentBundleΩ I M) (CotangentBundleVF I M) :=
  manifoldDFS (cotangentBundleModel I) (CotangentBundle I M)


/-- Instance witness for the differential form space structure on the cotangent bundle. -/
noncomputable instance instCotangentBundleDFS_DFS :
    DifferentialFormSpace (CotangentBundleΩ I M) (CotangentBundleVF I M) :=
  cotangentBundleDFSInst I M

end CotangentBundleDFSTypes


section CotangentBundleDFSInstance

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E]
variable {H : Type u} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable (M : Type u) [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

/-- The canonical (Liouville/tautological) $1$-form $\theta$ on $T^*M$, defined locally by $\theta_{(x,\xi)} = \xi \circ d\pi$. -/
end CotangentBundleDFSInstance


section Theorems

variable {EI : Type u} [NormedAddCommGroup EI] [NormedSpace ℝ EI]
  [FiniteDimensional ℝ EI] [Nontrivial EI]
variable {HI : Type u} [TopologicalSpace HI]
variable (I : ModelWithCorners ℝ EI HI)
variable (M : Type u) [TopologicalSpace M] [ChartedSpace HI M]
variable [IsManifold I ∞ M]

/-- Convenience abbreviation for the `CotangentBundleDFS` structure of $T^*M$. -/
end Theorems
