/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section30.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section26
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section33
import Def.v1.Atlas.AlgebraicTopologyI.code.Section33.Part2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Projection
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section30.Part2
open Matrix


noncomputable section

namespace SurfacesAndBilinearForms

open CategoryTheory AlgebraicTopology SingularCohomology

attribute [instance] CompactSurface.compact CompactSurface.connected
  CompactSurface.t2 CompactSurface.charted

/-- The underlying topological space of the connected sum `S₁ ♯ S₂` of two
compact surfaces: remove an open disk from each surface and glue along the
resulting boundary circles. -/
def orthogonalDirectSumForm
    {V₁ V₂ : Type} [AddCommGroup V₁] [Module (ZMod 2) V₁]
    [AddCommGroup V₂] [Module (ZMod 2) V₂]
    (B₁ : LinearMap.BilinForm (ZMod 2) V₁)
    (B₂ : LinearMap.BilinForm (ZMod 2) V₂) :
    LinearMap.BilinForm (ZMod 2) (V₁ × V₂) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => B₁ x.1 y.1 + B₂ x.2 y.2)
    (fun x₁ x₂ y => by
      simp only [map_add, LinearMap.add_apply, Prod.fst_add, Prod.snd_add]; ring)
    (fun r x y => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, Prod.smul_fst,
        Prod.smul_snd]; ring)
    (fun x y₁ y₂ => by
      simp only [map_add, Prod.fst_add, Prod.snd_add]; ring)
    (fun r x y => by
      simp only [map_smul, smul_eq_mul, Prod.smul_fst, Prod.smul_snd]; ring)

/-- The *punctured surface* `S ∖ B`: remove a small open disk from `S`
using a chart centred at an arbitrary point. -/
def puncturedSurface (S : CompactSurface) : TopCat.{0} :=
  let x : S.toTopCat := Classical.arbitrary _
  let φ := chartAt (EuclideanSpace ℝ (Fin 2)) x
  let U : Set S.toTopCat := φ.source ∩ ⇑φ ⁻¹' Metric.ball (φ x) 1
  TopCat.of ↥Uᶜ

/-- The continuous inclusion `S ∖ B ↪ S` of the punctured surface into
the original surface. -/
def puncturedSurfaceInclusion (S : CompactSurface) :
    puncturedSurface S ⟶ S.toTopCat :=
  ⟨Subtype.val, continuous_subtype_val⟩


/-- The inclusion of the punctured surface into the surface induces an
isomorphism on `H¹(–; F₂)` (removing an open disk does not change `H¹`). -/
def connectedSum_mv_restrictionMap (S₁ S₂ : CompactSurface) :
    CohomZMod2 (S₁ ♯ S₂).toTopCat 1 →ₗ[ZMod 2]
      CohomZMod2 (puncturedSurface S₁) 1 × CohomZMod2 (puncturedSurface S₂) 1 :=
  LinearMap.prod
    (singularCohomologyMap (ZMod 2)
      (puncturedSurfaceInclusionConnectedSum₁ S₁ S₂) 1).hom
    (singularCohomologyMap (ZMod 2)
      (puncturedSurfaceInclusionConnectedSum₂ S₁ S₂) 1).hom


/-- The Mayer–Vietoris connecting homomorphism in degree zero,
`H⁰(S¹; F₂) ≅ F₂ → H¹(S₁ ♯ S₂; F₂)`. -/
def connectedSum_mv_restrictionMap₀ (_S₁ _S₂ : CompactSurface) :
    ZMod 2 × ZMod 2 →ₗ[ZMod 2] ZMod 2 :=
  { toFun := fun p => p.1 + p.2
    map_add' := fun x y => by
      simp only [Prod.fst_add, Prod.snd_add]
      ring
    map_smul' := fun r x => by
      simp only [Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, smul_eq_mul]
      ring }

/-- Since the preceding restriction map is surjective, the connecting
homomorphism `δ⁰ : H⁰(S¹) → H¹(S₁ ♯ S₂)` is the zero map. -/
def CompactSurface.Homeomorphic (S₁ S₂ : CompactSurface) : Prop :=
  Nonempty (S₁.toTopCat ≃ₜ S₂.toTopCat)

/-- The set of *homeomorphism classes* of compact surfaces, as a quotient
of `CompactSurface` by the homeomorphism relation. -/
def SurfaceClass : Type 1 := Quot CompactSurface.Homeomorphic

/-- The canonical map sending a compact surface to its homeomorphism class. -/
def SurfaceClass.mk : CompactSurface → SurfaceClass := Quot.mk _

end SurfacesAndBilinearForms
end
