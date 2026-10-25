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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section33
open CategoryTheory AlgebraicTopology Limits


noncomputable section

open SingularCohomology

/-- The **Kronecker pairing** $\langle -, - \rangle : H^p(X; R) \otimes_R H_p(X; R) \to R$:
a cohomology class `β ∈ H^p(X; R)` is represented by a cocycle, a homology class
`x ∈ H_p(X; R)` is represented by a cycle, and the pairing evaluates the cocycle
on the cycle. The construction passes to homology by verifying that cocycles
vanish on boundaries and that coboundaries vanish on cycles. -/
def SingularCohomology.kroneckerPairing
    (R : Type) [CommRing R] (X : TopCat.{0}) (p : ℕ) :
    (SingularCohomology.singularCohomologyR R X p : Type) →ₗ[R]
    (SingularCohomology.singularHomologyModule R X p : Type) →ₗ[R] R := by

  set chainCx := singularChainCx R X
  set cochainCx := chainCx.linearYonedaObj R (ModuleCat.of R R)
  set Sc := chainCx.sc p
  set Scc := cochainCx.sc p

  set isoH := Sc.moduleCatHomologyIso
  set isoCH := Scc.moduleCatHomologyIso

  have h1 := down_prev_eq_up_next p
  have h2 := down_next_eq_up_prev p

  set rawEval : ∀ β : LinearMap.ker Scc.g.hom, LinearMap.ker Sc.g.hom →ₗ[R] R :=
    fun β => ((show chainCx.X p ⟶ ModuleCat.of R R from β.val).hom).comp
      (LinearMap.ker Sc.g.hom).subtype

  have h_cocycle : ∀ β : LinearMap.ker Scc.g.hom,
      LinearMap.range Sc.moduleCatToCycles ≤ LinearMap.ker (rawEval β) := by
    intro β x ⟨η, hη⟩; rw [LinearMap.mem_ker]; subst hη
    exact congr_arg (fun f => f.hom η)
      (show Sc.f ≫ (show chainCx.X p ⟶ ModuleCat.of R R from β.val) = 0 from by
        have hβ := β.prop; rw [LinearMap.mem_ker] at hβ
        let β' : chainCx.X p ⟶ ModuleCat.of R R := β.val
        rw [show Sc.f = chainCx.d ((ComplexShape.down ℕ).prev p) p from rfl,
            ← HomologicalComplex.XIsoOfEq_hom_comp_d chainCx h1 p]
        have key : chainCx.d ((ComplexShape.up ℕ).next p) p ≫ β' = 0 := hβ
        change ((HomologicalComplex.XIsoOfEq chainCx h1).hom ≫
          chainCx.d ((ComplexShape.up ℕ).next p) p) ≫ β' = 0
        rw [Category.assoc, key, comp_zero])

  set evalOnH := fun β : LinearMap.ker Scc.g.hom =>
    (LinearMap.range Sc.moduleCatToCycles).liftQ (rawEval β) (h_cocycle β)

  let outerMap : LinearMap.ker Scc.g.hom →ₗ[R]
      ((LinearMap.ker Sc.g.hom ⧸ LinearMap.range Sc.moduleCatToCycles) →ₗ[R] R) :=
    { toFun := evalOnH
      map_add' := fun β₁ β₂ => by
        ext ⟨ξ, hξ⟩
        show evalOnH (β₁ + β₂) (Submodule.Quotient.mk ⟨ξ, hξ⟩) =
          evalOnH β₁ (Submodule.Quotient.mk ⟨ξ, hξ⟩) + evalOnH β₂ (Submodule.Quotient.mk ⟨ξ, hξ⟩)
        simp only [evalOnH, Submodule.liftQ_apply, rawEval, LinearMap.coe_comp,
          Function.comp_apply]
        change (((β₁.val + β₂.val : chainCx.X p ⟶ ModuleCat.of R R).hom)) ξ =
          ((β₁.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ +
          ((β₂.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ
        change ((β₁.val : chainCx.X p ⟶ ModuleCat.of R R).hom +
          (β₂.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ = _
        simp [LinearMap.add_apply]
      map_smul' := fun r β => by
        ext ⟨ξ, hξ⟩
        show evalOnH (r • β) (Submodule.Quotient.mk ⟨ξ, hξ⟩) =
          r • evalOnH β (Submodule.Quotient.mk ⟨ξ, hξ⟩)
        simp only [evalOnH, Submodule.liftQ_apply, rawEval, LinearMap.coe_comp,
          Function.comp_apply, smul_eq_mul]
        change ((r • (β.val : chainCx.X p ⟶ ModuleCat.of R R)).hom) ξ =
          r * ((β.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ
        change (r • (β.val : chainCx.X p ⟶ ModuleCat.of R R).hom) ξ = _
        simp [LinearMap.smul_apply, smul_eq_mul] }

  have h_cobdy : LinearMap.range Scc.moduleCatToCycles ≤ LinearMap.ker outerMap := by
    intro x ⟨α, hα⟩; rw [LinearMap.mem_ker]; subst hα
    ext ⟨ξ, hξ⟩
    show evalOnH (Scc.moduleCatToCycles α) (Submodule.Quotient.mk ⟨ξ, hξ⟩) = 0
    simp only [evalOnH, Submodule.liftQ_apply, rawEval, LinearMap.coe_comp,
      Function.comp_apply]
    show ((show chainCx.X p ⟶ ModuleCat.of R R from (Scc.f.hom α)).hom) ξ = 0
    have step1 : (show chainCx.X p ⟶ ModuleCat.of R R from (Scc.f.hom α)) =
        chainCx.d p ((ComplexShape.up ℕ).prev p) ≫
        (show chainCx.X ((ComplexShape.up ℕ).prev p) ⟶ ModuleCat.of R R from α) := rfl
    rw [step1, ModuleCat.comp_apply,
      show chainCx.d p ((ComplexShape.up ℕ).prev p) =
        chainCx.d p ((ComplexShape.down ℕ).next p) ≫
        (HomologicalComplex.XIsoOfEq chainCx h2).hom from
      (HomologicalComplex.d_comp_XIsoOfEq_hom chainCx h2 p).symm,
      ModuleCat.comp_apply,
      show (chainCx.d p ((ComplexShape.down ℕ).next p)).hom ξ = Sc.g.hom ξ from rfl]
    rw [LinearMap.mem_ker] at hξ
    erw [hξ, map_zero]

  set pairingConcrete :=
    (LinearMap.range Scc.moduleCatToCycles).liftQ outerMap h_cobdy
  exact
    { toFun := fun β_abs =>
        (pairingConcrete (isoCH.hom.hom β_abs)).comp isoH.hom.hom
      map_add' := fun β₁ β₂ => by
        ext x; simp only [LinearMap.comp_apply, LinearMap.add_apply]
        erw [map_add, map_add]; rfl
      map_smul' := fun r β => by
        ext x; simp only [LinearMap.comp_apply, LinearMap.smul_apply, RingHom.id_apply]
        erw [map_smul, map_smul]; rfl }

end

set_option maxHeartbeats 1600000 in


open SingularCohomology in
/-- The **homology cross product**
$\times : H_p(X; R) \otimes_R H_q(Y; R) \to H_{p+q}(X \times Y; R)$,
constructed via the Eilenberg–Zilber / Alexander–Whitney machinery. -/
noncomputable def SingularCohomology.homologyCross
    (R : Type) [CommRing R] (X Y : TopCat.{0}) (p q : ℕ) :
    TensorProduct R (↑(singularHomologyModule R X p))
      (↑(singularHomologyModule R Y q)) →ₗ[R]
      ↑(singularHomologyModule R (TopCat.of (↑X × ↑Y)) (p + q)) :=
  (homologyCrossProductDeg R X Y p q).hom

open SingularCohomology in
/-- The **cohomology cross product**
$\times : H^p(X; R) \otimes_R H^q(Y; R) \to H^{p+q}(X \times Y; R)$,
defined via the Alexander–Whitney cup product on the categorical product
followed by transport along `TopCat.prodIsoProd`. -/
noncomputable def SingularCohomology.cohomologyCross
    (R : Type) [CommRing R] (X Y : TopCat.{0}) (p q : ℕ) :
    TensorProduct R (↑(singularCohomology R X (ModuleCat.of R R) p))
      (↑(singularCohomology R Y (ModuleCat.of R R) q)) →ₗ[R]
      ↑(singularCohomology R (TopCat.of (↑X × ↑Y)) (ModuleCat.of R R) (p + q)) :=
  (cohomologyCrossProduct R X Y p q ≫
    singularCohomologyMap R (TopCat.prodIsoProd X Y).inv (p + q)).hom

