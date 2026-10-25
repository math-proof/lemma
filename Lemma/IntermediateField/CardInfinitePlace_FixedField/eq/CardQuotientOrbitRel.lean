import Mathlib
import sympy.Basic
import Lemma.NumberField.ArchimedeanIdeleModule
import Lemma.Int.P2MUtil

open IsDedekindDomain NumberField

/--
[NumberField_InfPlaceDecomp_card_infinitePlace_fixedField_eq_card_orbitRel_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NumberField_InfPlaceDecomp_card_infinitePlace_fixedField_eq_card_orbitRel_quotient.lean)
-/

def sigmaOrbitEquiv {G : Type*} [Group G] (H : Subgroup G) {ι : Type*} (X : ι → Type*) [∀ i, MulAction G (X i)] :
    MulAction.orbitRel.Quotient H (Σ i, X i) ≃ Σ i, MulAction.orbitRel.Quotient H (X i) where
  toFun := Quotient.lift (fun x : Σ i, X i => (⟨x.1, (Quotient.mk'' x.2 : MulAction.orbitRel.Quotient H (X x.1))⟩ :
      Σ i, MulAction.orbitRel.Quotient H (X i))) (by
    rintro a ⟨i, x⟩ hab
    obtain ⟨h, rfl⟩ := MulAction.orbitRel_apply.1 hab
    change (⟨i, Quotient.mk'' (h • x)⟩ : Σ i, MulAction.orbitRel.Quotient H (X i)) = ⟨i, Quotient.mk'' x⟩
    exact congrArg (Sigma.mk i) (Quotient.sound' (MulAction.mem_orbit x h)))
  invFun p := Quotient.map' (Sigma.mk p.1) (fun a b hab => by
    obtain ⟨h, rfl⟩ := MulAction.orbitRel_apply.1 hab
    exact MulAction.orbitRel_apply.2 ⟨h, rfl⟩) p.2
  left_inv q := Quotient.inductionOn' q fun x => by rcases x with ⟨i, x⟩; rfl
  right_inv p := by
    rcases p with ⟨i, q⟩
    induction q using Quotient.inductionOn' with
    | h x => rfl

private lemma  nonempty_orbitQuot_equiv {G : Type*} [Group G] (H : Subgroup G) {α : Type*} [MulAction G α]
    (ω : MulAction.orbitRel.Quotient G α) (a : α) (ha : Quotient.mk'' a = ω) :
    Nonempty (MulAction.orbitRel.Quotient H ω.orbit ≃ MulAction.orbitRel.Quotient H (G ⧸ MulAction.stabilizer G a)) := by
  subst ha
  let e : MulAction.orbitRel.Quotient.orbit (Quotient.mk'' a : MulAction.orbitRel.Quotient G α) ≃ G ⧸ MulAction.stabilizer G a :=
    MulAction.orbitEquivQuotientStabilizer G a
  have hsymm : ∀ (g : G) (q : G ⧸ MulAction.stabilizer G a), e.symm (g • q) = g • e.symm q := by
    intro g q
    induction q using QuotientGroup.induction_on with
    | H b =>
      apply Subtype.ext
      change ((MulAction.orbitEquivQuotientStabilizer G a).symm (g • (b : G ⧸ MulAction.stabilizer G a)) : α) =
        g • ((MulAction.orbitEquivQuotientStabilizer G a).symm (b : G ⧸ MulAction.stabilizer G a) : α)
      rw [MulAction.Quotient.smul_coe, smul_eq_mul, MulAction.orbitEquivQuotientStabilizer_symm_apply,
        MulAction.orbitEquivQuotientStabilizer_symm_apply, mul_smul]
  have hsmul : ∀ (g : G) (x : MulAction.orbitRel.Quotient.orbit (Quotient.mk'' a : MulAction.orbitRel.Quotient G α)),
      e (g • x) = g • e x := by
    intro g x
    apply e.symm.injective
    rw [Equiv.symm_apply_apply, hsymm, Equiv.symm_apply_apply]
  refine ⟨Quotient.congr e fun x y => ?_⟩
  rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, (hsmul h y).symm⟩
  · rintro ⟨h, hh⟩
    refine ⟨h, e.injective ?_⟩
    rw [← hh]
    exact hsmul h y
@[path]
private lemma main
  {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
  {H : Subgroup (K ≃ₐ[E] K)} :
-- imply
  Nat.card (InfinitePlace (IntermediateField.fixedField H)) =
      Nat.card (MulAction.orbitRel.Quotient H
        (Σ v : InfinitePlace E, (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v))) := by
-- proof
  classical

  set G := K ≃ₐ[E] K
  set F := IntermediateField.fixedField H
  have hH : F.fixingSubgroup = H := IntermediateField.fixingSubgroup_fixedField H

  rw [← Nat.card_congr (NumberField.InfinitePlace.orbitRelEquiv (k := F) (K := K))]

  have horb : ∀ w w' : InfinitePlace K, w' ∈ MulAction.orbit (K ≃ₐ[F] K) w ↔ w' ∈ MulAction.orbit H w := by
    intro w w'
    constructor
    · rintro ⟨τ, rfl⟩
      have hmem : τ.restrictScalars E ∈ H := by
        apply hH.le
        rw [IntermediateField.mem_fixingSubgroup_iff]
        intro x hx
        exact τ.commutes ⟨x, hx⟩
      exact ⟨⟨τ.restrictScalars E, hmem⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      refine ⟨IntermediateField.fixingSubgroupEquiv F ⟨h, hH.ge h.2⟩, ?_⟩
      rfl
  have e2 : Quotient (MulAction.orbitRel (K ≃ₐ[F] K) (InfinitePlace K)) ≃ MulAction.orbitRel.Quotient H (InfinitePlace K) :=
    Quotient.congrRight fun w w' => by
      rw [MulAction.orbitRel_apply, MulAction.orbitRel_apply]
      exact horb w' w
  rw [Nat.card_congr e2]

  rw [Nat.card_congr (MulAction.equivSubgroupOrbits (InfinitePlace K) H), Nat.card_sigma,
    Nat.card_congr (sigmaOrbitEquiv H fun v : InfinitePlace E =>
      G ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)), Nat.card_sigma]

  refine Fintype.sum_equiv (NumberField.InfinitePlace.orbitRelEquiv (k := E) (K := K)) _ _ fun ω => ?_
  have hω : Quotient.mk'' (NumberField.ArchIdele.above E K (NumberField.InfinitePlace.orbitRelEquiv ω)) = ω := by
    apply (NumberField.InfinitePlace.orbitRelEquiv (k := E) (K := K)).injective
    rw [NumberField.InfinitePlace.orbitRelEquiv_apply_mk'', NumberField.ArchIdele.comap_above]
  exact Nat.card_congr (nonempty_orbitQuot_equiv H ω _ hω).some


-- created on 2026-10-23
