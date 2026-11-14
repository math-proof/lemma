import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Subgroup.Actions
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.GroupTheory.GroupAction.Quotient
import Instance.AbstractHeckeOperator

variable {G : Type*} [Group G] {A : Type*} [AddCommMonoid A]
    [DistribMulAction G A] {g : G} {U V : Subgroup G}

open MulAction
open scoped Pointwise

variable (h : (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)).Finite)

open ConjAct

namespace AbstractHeckeOperator

noncomputable def HeckeOperator_toFun (a : fixedPoints V A) : fixedPoints U A :=
  have bijOn_smul (X : Set G) {u : G} (hu : u ∈ U) :
      Set.BijOn (fun x ↦ u • x) ((U : Set G) * X) (U * X) := by
    refine ⟨?_, Set.injOn_of_injective (MulAction.injective u), ?_⟩
    · rintro x ⟨u', hu', x, hx, rfl⟩
      exact ⟨u * u', mul_mem hu hu', x, hx, by simp [mul_assoc]⟩
    · rintro x ⟨u', hu', x, hx, rfl⟩
      exact ⟨(u⁻¹ * u') * x, ⟨u⁻¹ * u', mul_mem (inv_mem hu) hu', x, hx, rfl⟩, by simp [mul_assoc]⟩
  have eq_finsum_quotient_out_of_bijOn'
      {X : Set (G ⧸ V)}
      {s : Set G} (hs : s.BijOn (QuotientGroup.mk : G → G ⧸ V) X) :
      ∑ᶠ g ∈ s, g • (a : A) = ∑ᶠ g ∈ Quotient.out '' X, g • (a : A) := by
    let e (g : G) : G := Quotient.out (QuotientGroup.mk g : G ⧸ V)
    have he₀ : Set.BijOn e s (Quotient.out '' X) := by
      refine Set.BijOn.comp ?_ hs
      exact Set.InjOn.bijOn_image <| Set.injOn_of_injective Quotient.out_injective
    have he₁ : ∀ g ∈ s, g • (a : A) = (Quotient.out (QuotientGroup.mk g : G ⧸ V)) • a := by
      intro g hgs
      obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul V g
      rw [hv, mul_smul, (show (v : G) • (a : A) = a from a.2 v)]
    exact finsum_mem_eq_of_bijOn e he₀ he₁
  ⟨∑ᶠ gᵢ ∈ Quotient.out '' (QuotientGroup.mk '' (U * {g}) : Set (G ⧸ V)), gᵢ • a.1, by
  rintro ⟨u, huU⟩
  rw [smul_finsum_mem (h.image Quotient.out), ← eq_finsum_quotient_out_of_bijOn']
  · rw [finsum_mem_eq_of_bijOn (fun g ↦ u • g)]
    · exact Set.InjOn.bijOn_image <| Set.injOn_of_injective (MulAction.injective u)
    · simp [mul_smul]
  · apply (Set.bijOn_comp_iff (Set.injOn_of_injective (MulAction.injective u))).1
    change Set.BijOn ((fun xbar ↦ u • xbar) ∘ (QuotientGroup.mk : G → G ⧸ V)) _ _
    rw [Set.bijOn_comp_iff]
    · rw [← Set.image_comp]
      simp only [Function.comp_apply, Quotient.out_eq, Set.image_id']
      refine Set.bijOn_image_image (f := fun (x : G) ↦ u • x) (p₁ := (QuotientGroup.mk : G → G ⧸ V))
        (fun a ↦ rfl) ?_ (Set.injOn_of_injective (MulAction.injective u))
      apply bijOn_smul _ huU
    · refine Set.InjOn.image_of_comp ?_
      simp only [Function.comp_def, Quotient.out_eq]
      exact Function.Injective.injOn Function.injective_id
    ⟩

noncomputable def HeckeOperator_addMonoidHom : fixedPoints V A →+ fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_zero' := by
    ext
    sorry
  map_add' a b := by
    have coe_add_U (x y : fixedPoints U A) :
        ((x + y : fixedPoints U A) : A) = x + y := rfl
    have coe_add_V (x y : fixedPoints V A) :
        ((x + y : fixedPoints V A) : A) = x + y := rfl
    ext
    simp only [HeckeOperator_toFun, coe_add_U, coe_add_V, smul_add,
      finsum_mem_add_distrib (h.image Quotient.out)]

variable {R : Type*} [Ring R] [Module R A] [SMulCommClass G R A]

variable (g U V) in

noncomputable def HeckeOperator : fixedPoints V A →ₗ[R] fixedPoints U A where
  toFun := HeckeOperator_toFun h
  map_add' a b := by
    have coe_add_U (x y : fixedPoints U A) :
        ((x + y : fixedPoints U A) : A) = x + y := rfl
    have coe_add_V (x y : fixedPoints V A) :
        ((x + y : fixedPoints V A) : A) = x + y := rfl
    ext
    simp only [HeckeOperator_toFun, coe_add_U, coe_add_V, smul_add,
      finsum_mem_add_distrib (h.image Quotient.out)]
  map_smul' r a := by
    have coe_smul_U (r : R) (x : fixedPoints U A) :
        ((r • x : fixedPoints U A) : A) = r • x := rfl
    have coe_smul_V (r : R) (x : fixedPoints V A) :
        ((r • x : fixedPoints V A) : A) = r • x := rfl
    ext
    simp only [HeckeOperator_toFun, coe_smul_U, coe_smul_V, smul_comm,
      smul_finsum_mem (h.image Quotient.out), RingHom.id_apply]

end AbstractHeckeOperator
