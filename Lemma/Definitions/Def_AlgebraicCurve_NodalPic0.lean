import Lemma.Definitions.Def_AlgebraicCurve_GluedPic0

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

section Nodal

variable (K : Type*) [Field K] {n m : ℕ} (Fbar : Fin n → Type*) [∀ i, Field (Fbar i)] [∀ i, Algebra K (Fbar i)]

abbrev NodalData : Type _ := ∀ i : Fin n, Divisor K (Fbar i)

namespace NodalData

variable {K Fbar}
variable (src tgt : Fin m → Fin n) (xs : ∀ e, Place K (Fbar (src e))) (xt : ∀ e, Place K (Fbar (tgt e)))

def admissible : AddSubgroup (NodalData K Fbar) where
  carrier := {E | (∀ i, E i ∈ Divisor.degZero (K := K) (F := Fbar i)) ∧
    ∀ e, E (src e) (xs e) = 0 ∧ E (tgt e) (xt e) = 0}
  zero_mem' := ⟨fun _ => zero_mem _, fun _ => ⟨rfl, rfl⟩⟩
  add_mem' := by
    rintro E E' ⟨hE, hEn⟩ ⟨hE', hE'n⟩
    refine ⟨fun i => add_mem (hE i) (hE' i), fun e => ⟨?_, ?_⟩⟩
    · rw [Pi.add_apply, Finsupp.add_apply, (hEn e).1, (hE'n e).1, add_zero]
    · rw [Pi.add_apply, Finsupp.add_apply, (hEn e).2, (hE'n e).2, add_zero]
  neg_mem' := by
    rintro E ⟨hE, hEn⟩
    refine ⟨fun i => neg_mem (hE i), fun e => ⟨?_, ?_⟩⟩
    · rw [Pi.neg_apply, Finsupp.neg_apply, (hEn e).1, neg_zero]
    · rw [Pi.neg_apply, Finsupp.neg_apply, (hEn e).2, neg_zero]

theorem mem_admissible {E : NodalData K Fbar} :
    E ∈ admissible src tgt xs xt ↔ (∀ i, E i ∈ Divisor.degZero (K := K) (F := Fbar i)) ∧
      ∀ e, E (src e) (xs e) = 0 ∧ E (tgt e) (xt e) = 0 :=
  Iff.rfl

def IsNodalPrincipal (E : NodalData K Fbar) : Prop :=
  ∃ (g : ∀ i, Fbar i) (a : Fin m → Kˣ), (∀ i, g i ≠ 0) ∧
    (∀ i, ∀ v : Place K (Fbar i), E i v = v.ord (g i)) ∧
    ∀ e, (xs e).HasValue (g (src e)) (a e) ∧ (xt e).HasValue (g (tgt e)) (a e)

def nodalPrincipal : AddSubgroup (NodalData K Fbar) where
  carrier := {E | IsNodalPrincipal src tgt xs xt E}
  zero_mem' := by
    refine ⟨fun _ => 1, fun _ => 1, fun _ => one_ne_zero, fun i v => by simp, fun e => ⟨?_, ?_⟩⟩
    · simpa using (xs e).hasValue_one
    · simpa using (xt e).hasValue_one
  add_mem' := by
    rintro E E' ⟨g, a, hg, hE, hv⟩ ⟨g', a', hg', hE', hv'⟩
    refine ⟨fun i => g i * g' i, a * a', fun i => mul_ne_zero (hg i) (hg' i), fun i v => ?_, fun e => ⟨?_, ?_⟩⟩
    · rw [Pi.add_apply, Finsupp.add_apply, hE i v, hE' i v, v.ord_mul (hg i) (hg' i)]
    · simpa only [Pi.mul_apply, Units.val_mul] using (hv e).1.mul (hv' e).1
    · simpa only [Pi.mul_apply, Units.val_mul] using (hv e).2.mul (hv' e).2
  neg_mem' := by
    rintro E ⟨g, a, hg, hE, hv⟩
    refine ⟨fun i => (g i)⁻¹, a⁻¹, fun i => inv_ne_zero (hg i), fun i v => ?_, fun e => ⟨?_, ?_⟩⟩
    · rw [Pi.neg_apply, Finsupp.neg_apply, hE i v, v.ord_inv]
    · simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using (hv e).1.inv (a e).ne_zero
    · simpa only [Pi.inv_apply, Units.val_inv_eq_inv_val] using (hv e).2.inv (a e).ne_zero

theorem mem_nodalPrincipal {E : NodalData K Fbar} :
    E ∈ nodalPrincipal src tgt xs xt ↔ IsNodalPrincipal src tgt xs xt E :=
  Iff.rfl

end NodalData

abbrev NodalPic0 (src tgt : Fin m → Fin n) (xs : ∀ e, Place K (Fbar (src e))) (xt : ∀ e, Place K (Fbar (tgt e))) : Type _ :=
  ↥(NodalData.admissible (K := K) (Fbar := Fbar) src tgt xs xt) ⧸
    (NodalData.nodalPrincipal (K := K) (Fbar := Fbar) src tgt xs xt).addSubgroupOf (NodalData.admissible src tgt xs xt)

namespace NodalPic0

variable {K Fbar}
variable (src tgt : Fin m → Fin n) (xs : ∀ e, Place K (Fbar (src e))) (xt : ∀ e, Place K (Fbar (tgt e)))

def mk : ↥(NodalData.admissible (K := K) (Fbar := Fbar) src tgt xs xt) →+ NodalPic0 K Fbar src tgt xs xt :=
  QuotientAddGroup.mk' _

theorem mk_surjective : Function.Surjective (mk (K := K) (Fbar := Fbar) src tgt xs xt) :=
  QuotientAddGroup.mk'_surjective _

theorem mk_eq_zero_iff (E : ↥(NodalData.admissible (K := K) (Fbar := Fbar) src tgt xs xt)) :
    mk src tgt xs xt E = 0 ↔ NodalData.IsNodalPrincipal src tgt xs xt (E : NodalData K Fbar) := by
  rw [mk, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
  rfl

end NodalPic0

end Nodal

end AlgebraicCurve
