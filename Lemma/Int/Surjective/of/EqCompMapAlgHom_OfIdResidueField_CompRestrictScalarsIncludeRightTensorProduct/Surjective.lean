import Mathlib
import sympy.Basic

open IsLocalRing
open scoped TensorProduct

/--
[AddMonoidAlgebra_surjective_of_surjective_residueField_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidAlgebra_surjective_of_surjective_residueField_comp.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsLocalRing R]
  {H : Type u} [CommRing H] [Algebra R H]
  {M : Type v} [AddCommMonoid M] [Finite M]
  {ψ : H →ₐ[R] AddMonoidAlgebra R M}
  {ψ₀ : ResidueField R ⊗[R] H →ₐ[ResidueField R] AddMonoidAlgebra (ResidueField R) M}
-- given
  (hψ₀ : Function.Surjective ψ₀)
  (hred : (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R))).comp ψ = (ψ₀.restrictScalars R).comp Algebra.TensorProduct.includeRight) :
-- imply
  Function.Surjective ψ := by
-- proof
  classical

  let S : Submodule R (AddMonoidAlgebra R M) := LinearMap.range ψ.toLinearMap
  suffices htop : (⊤ : Submodule R (AddMonoidAlgebra R M)) ≤ S by
    intro y
    obtain ⟨x, hx⟩ := htop (Submodule.mem_top : y ∈ ⊤)
    exact ⟨x, hx⟩
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal R) Module.Finite.fg_top
    (IsLocalRing.maximalIdeal_le_jacobson ⊥) ?_

  intro x _
  have hsurjR : Function.Surjective (algebraMap R (ResidueField R)) := IsLocalRing.residue_surjective
  obtain ⟨t, ht⟩ := hψ₀ (AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) x)
  obtain ⟨h, rfl⟩ := Algebra.TensorProduct.includeRight_surjective H hsurjR t
  have hπ : AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) (ψ h) =
      AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) x := by
    have e := congrArg (fun φ : H →ₐ[R] AddMonoidAlgebra (ResidueField R) M => φ h) hred
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at e
    rw [e, ht]

  set z : AddMonoidAlgebra R M := x - ψ h with hzdef
  have hz0 : AddMonoidAlgebra.mapAlgHom M (Algebra.ofId R (ResidueField R)) z = 0 := by
    rw [hzdef, map_sub, hπ, sub_self]
  have hcoef : ∀ m : M, z.coeff m ∈ maximalIdeal R := fun m => by
    have e := congrArg (fun w : AddMonoidAlgebra (ResidueField R) M => w.coeff m) hz0
    simp only [AddMonoidAlgebra.coeff_mapAlgHom, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero,
      Pi.zero_apply] at e
    exact (IsLocalRing.residue_eq_zero_iff (z.coeff m)).mp e
  have hzmem : z ∈ maximalIdeal R • (⊤ : Submodule R (AddMonoidAlgebra R M)) := by
    rw [← AddMonoidAlgebra.sum_coeff_single z]
    refine Submodule.sum_mem _ (fun m _ => ?_)
    show AddMonoidAlgebra.single m (z.coeff m) ∈ maximalIdeal R • (⊤ : Submodule R (AddMonoidAlgebra R M))
    have h : AddMonoidAlgebra.single m (z.coeff m) = (z.coeff m) • AddMonoidAlgebra.single m (1 : R) := by
      rw [AddMonoidAlgebra.smul_single', mul_one]
    rw [h]
    exact Submodule.smul_mem_smul (hcoef m) Submodule.mem_top
  have hx : x = ψ h + z := by rw [hzdef]; abel
  rw [hx]
  exact Submodule.add_mem_sup (LinearMap.mem_range_self ψ.toLinearMap h) hzmem


-- created on 2026-10-09
