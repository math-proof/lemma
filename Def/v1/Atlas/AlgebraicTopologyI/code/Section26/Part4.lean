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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section26
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology


namespace SingularCohomology

/-- The Alexander–Whitney bilinear cup product on cochains:
$(f \cup g)(\sigma) = f(\sigma \circ \alpha_p) \cdot g(\sigma \circ \omega_q)$. -/
def cupBilinear (R : Type) [CommRing R] (Z : TopCat.{0}) (p q : ℕ) :
    (singularCochainComplex R Z (ModuleCat.of R R)).X p →ₗ[R]
    (singularCochainComplex R Z (ModuleCat.of R R)).X q →ₗ[R]
    (singularCochainComplex R Z (ModuleCat.of R R)).X (p + q) :=
  LinearMap.mk₂ R
    (fun f g => Sigma.desc fun σ =>
      ModuleCat.ofHom ((evalAtSimplex R Z (awFront Z p q σ) f *
        evalAtSimplex R Z (awBack Z p q σ) g) • LinearMap.id))
    (fun f₁ f₂ g => by
      apply Limits.Sigma.hom_ext; intro b
      erw [Preadditive.comp_add, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      apply ModuleCat.hom_ext
      show ((evalAtSimplex R Z (awFront Z p q b) (f₁ + f₂) * _) • (LinearMap.id : R →ₗ[R] R)) = _
      rw [map_add, add_mul, add_smul, ofHom_add_hom_eq R])
    (fun c f g => by
      apply Limits.Sigma.hom_ext; intro b
      erw [Linear.comp_smul, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      apply ModuleCat.hom_ext; ext
      show ((evalAtSimplex R Z (awFront Z p q b) (c • f) * _) • (LinearMap.id : R →ₗ[R] R)) _ = _
      change (c * evalAtSimplex R Z (awFront Z p q b) f *
        evalAtSimplex R Z (awBack Z p q b) g) * _ = _
      show _ = (c • ((evalAtSimplex R Z (awFront Z p q b) f *
        evalAtSimplex R Z (awBack Z p q b) g) • (LinearMap.id : R →ₗ[R] R))) 1
      simp [smul_eq_mul]; ring)
    (fun f g₁ g₂ => by
      apply Limits.Sigma.hom_ext; intro b
      erw [Preadditive.comp_add, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      apply ModuleCat.hom_ext
      show ((_ * evalAtSimplex R Z (awBack Z p q b) (g₁ + g₂)) • (LinearMap.id : R →ₗ[R] R)) = _
      rw [map_add, mul_add, add_smul, ofHom_add_hom_eq R])
    (fun c f g => by
      apply Limits.Sigma.hom_ext; intro b
      erw [Linear.comp_smul, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc]
      apply ModuleCat.hom_ext; ext
      show ((_ * evalAtSimplex R Z (awBack Z p q b) (c • g)) • (LinearMap.id : R →ₗ[R] R)) _ = _
      change (evalAtSimplex R Z (awFront Z p q b) f * (c *
        evalAtSimplex R Z (awBack Z p q b) g)) * _ = _
      show _ = (c • ((evalAtSimplex R Z (awFront Z p q b) f *
        evalAtSimplex R Z (awBack Z p q b) g) • (LinearMap.id : R →ₗ[R] R))) 1
      simp [smul_eq_mul]; ring)

/-- The Alexander–Whitney cup product on cochains, packaged as a morphism out of the tensor
product $S^p(Z) \otimes S^q(Z) \to S^{p+q}(Z)$. -/
def awCochainPairingHom
    (R : Type) [CommRing R] (Z : TopCat.{0}) (p q : ℕ) :
    (singularCochainComplex R Z (ModuleCat.of R R)).X p ⊗
    (singularCochainComplex R Z (ModuleCat.of R R)).X q ⟶
    (singularCochainComplex R Z (ModuleCat.of R R)).X (p + q) :=
  ModuleCat.ofHom (TensorProduct.lift (cupBilinear R Z p q))


/-- The Leibniz rule for the cup product on cochains:
$d(f \cup g) = df \cup g + (-1)^p f \cup dg$. -/

section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000

/-- The zeroth singular cohomology `H^0(X; N)` is naturally isomorphic to the
kernel of the coboundary `d^0 : C^0(X; N) → C^1(X; N)`. -/
noncomputable def singularCohomologyZeroIsoKer (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    singularCohomology ℤ X N 0 ≅
    @ModuleCat.of ℤ Int.instCommRing.toRing
      (LinearMap.ker ((singularCochainComplex ℤ X N).sc' 0 0 1).g.hom)
      ((singularCochainComplex ℤ X N).sc' 0 0 1).g.hom.ker.addCommGroup
      ((singularCochainComplex ℤ X N).sc' 0 0 1).g.hom.ker.module :=
  (CochainComplex.isoHomologyπ₀ (singularCochainComplex ℤ X N)).symm ≪≫
    (singularCochainComplex ℤ X N).cyclesIsoSc' 0 0 1
      CochainComplex.prev_nat_zero (CochainComplex.next ℕ 0) ≪≫
    ((singularCochainComplex ℤ X N).sc' 0 0 1).cyclesIsoKernel ≪≫
    ModuleCat.kernelIsoKer ((singularCochainComplex ℤ X N).sc' 0 0 1).g

end

/-- The submodule of `N`-valued functions on `X` that are constant on path
components: `f x = f y` whenever `x` and `y` are joined by a path. -/
def pathConstantSubmodule (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) : Submodule ℤ (X → N) where
  carrier := {f | ∀ x y : X, Joined x y → f x = f y}
  add_mem' {f g} hf hg x y hxy := by
    show f x + g x = f y + g y
    rw [hf x y hxy, hg x y hxy]
  zero_mem' _ _ _ := rfl
  smul_mem' c f hf x y hxy := by
    show c • f x = c • f y
    rw [hf x y hxy]

/-- A function constant on path components is the same as a function on the
set of path components `π₀(X)`. -/
noncomputable def pathConstantSubmoduleEquivPi0Func (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    (pathConstantSubmodule X N) ≃ₗ[ℤ] (ZerothHomotopy X → N) where
  toFun := fun ⟨f, hf⟩ => Quotient.lift f (fun a b hab => hf a b hab)
  invFun := fun g => ⟨fun x => g (Quotient.mk (pathSetoid X) x),
      fun x y hxy => congrArg g (Quotient.sound hxy)⟩
  left_inv := fun ⟨f, hf⟩ => by
    ext x
    simp only [Quotient.lift_mk]
  right_inv := fun g => by
    ext q
    exact Quotient.inductionOn q (fun x => rfl)
  map_add' := fun ⟨f, hf⟩ ⟨g, hg⟩ => by
    ext q
    exact Quotient.inductionOn q (fun x => rfl)
  map_smul' := fun c ⟨f, hf⟩ => by
    ext q
    exact Quotient.inductionOn q (fun x => rfl)

/-- Convenience alias for `pathConstantSubmoduleEquivPi0Func` viewed as a
linear equivalence on the coerced submodule. -/
noncomputable def pathConstantEquivPi0Func (X : TopCat.{0}) (N : ModuleCat.{0} ℤ) :
    ↥(pathConstantSubmodule X N) ≃ₗ[ℤ] (ZerothHomotopy X → N) :=
  pathConstantSubmoduleEquivPi0Func X N

end SingularCohomology
