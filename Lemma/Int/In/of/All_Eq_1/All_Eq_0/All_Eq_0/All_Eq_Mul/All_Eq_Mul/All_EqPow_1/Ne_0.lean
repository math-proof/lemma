import Mathlib
import sympy.Basic

open AddSubgroup

/--
[AddSubgroup_mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddSubgroup_mem_of_forall_pairing_annihilator_eq_one_of_nondegenerate.lean)
-/

private lemma  finite_monoidHom (K : Type*) [CommGroup K] [Finite K] (L : Type*) [Field L] : Finite (K →* L) := by
  have := Fintype.ofFinite K
  exact (linearIndependent_monoidHom K L).finite

private lemma  card_monoidHom_le (K : Type*) [CommGroup K] [Finite K] (L : Type*) [Field L] :
  Nat.card (K →* L) ≤ Nat.card K := by
  classical
  have := Fintype.ofFinite K
  have hli := linearIndependent_monoidHom K L
  have : Finite (K →* L) := hli.finite
  have := Fintype.ofFinite (K →* L)
  have h2 : Fintype.card (K →* L) ≤ Fintype.card K := by
    have := hli.fintype_card_le_finrank
    rwa [Module.finrank_fintype_fun_eq_card] at this
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]


@[path]
private lemma main
  [AddCommGroup G] [Finite G] [Field L]
  {n : ℕ}
  {B : G → G → L}
  {A : AddSubgroup G}
  {x : G}
-- given
  (hn : n ≠ 0)
  (hval : ∀ x y : G, B x y ^ n = 1)
  (hadd₁ : ∀ x x' y : G, B (x + x') y = B x y * B x' y)
  (hadd₂ : ∀ x y y' : G, B x (y + y') = B x y * B x y')
  (hleft : ∀ x : G, (∀ y : G, B x y = 1) → x = 0)
  (_ : ∀ y : G, (∀ x : G, B x y = 1) → y = 0)
  (hx : ∀ y : G, (∀ a ∈ A, B a y = 1) → B x y = 1) :
-- imply
  x ∈ A := by
-- proof
  classical
  have := Fintype.ofFinite G

  have hB0 : ∀ x y : G, B x y ≠ 0 := fun x y h => by
    have := hval x y; rw [h, zero_pow hn] at this; exact zero_ne_one this
  have hzero₁ : ∀ y : G, B 0 y = 1 := fun y => by
    have h := hadd₁ 0 0 y
    rw [add_zero] at h
    exact (mul_left_cancel₀ (hB0 0 y) (by rwa [mul_one])).symm
  have hzero₂ : ∀ x : G, B x 0 = 1 := fun x => by
    have h := hadd₂ x 0 0
    rw [add_zero] at h
    exact (mul_left_cancel₀ (hB0 x 0) (by rwa [mul_one])).symm
  have hneg₂ : ∀ x y : G, B x (-y) = (B x y)⁻¹ := fun x y => by
    have h := hadd₂ x y (-y)
    rw [add_neg_cancel, hzero₂] at h
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)
  have hneg₁ : ∀ x y : G, B (-x) y = (B x y)⁻¹ := fun x y => by
    have h := hadd₁ x (-x) y
    rw [add_neg_cancel, hzero₁] at h
    exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)

  let Ap : AddSubgroup G :=
    { carrier := {y | ∀ a ∈ A, B a y = 1}
      zero_mem' := fun a _ => hzero₂ a
      add_mem' := fun {y y'} hy hy' a ha => by rw [hadd₂, hy a ha, hy' a ha, one_mul]
      neg_mem' := fun {y} hy a ha => by rw [hneg₂, hy a ha, inv_one] }
  have mem_Ap : ∀ y : G, y ∈ Ap ↔ ∀ a ∈ A, B a y = 1 := fun _ => Iff.rfl
  let App : AddSubgroup G :=
    { carrier := {x | ∀ z ∈ Ap, B x z = 1}
      zero_mem' := fun z _ => hzero₁ z
      add_mem' := fun {x x'} hx hx' z hz => by rw [hadd₁, hx z hz, hx' z hz, one_mul]
      neg_mem' := fun {x} hx z hz => by rw [hneg₁, hx z hz, inv_one] }
  have mem_App : ∀ x : G, x ∈ App ↔ ∀ z ∈ Ap, B x z = 1 := fun _ => Iff.rfl
  have hAle : A ≤ App := fun a ha z hz => hz a ha
  have hxmem : x ∈ App := fun z hz => hx z hz

  have hwd : ∀ x : G, (∀ z ∈ Ap, B x z = 1) → ∀ y y' : G, (QuotientAddGroup.mk y : G ⧸ Ap) = QuotientAddGroup.mk y' → B x y = B x y' := by
    intro x hx y y' h
    rw [QuotientAddGroup.eq] at h
    have := hx _ h
    rwa [hadd₂, hneg₂, inv_mul_eq_one₀ (hB0 x y)] at this

  let ρ₀ : G → (Multiplicative A →* L) := fun y =>
    { toFun := fun a => B ((Multiplicative.toAdd a : A) : G) y
      map_one' := hzero₁ y
      map_mul' := fun a b => hadd₁ _ _ y }
  have hρ₀ : ∀ y y' : G, ρ₀ y = ρ₀ y' → (QuotientAddGroup.mk y : G ⧸ Ap) = QuotientAddGroup.mk y' := by
    intro y y' h
    rw [QuotientAddGroup.eq, mem_Ap]
    intro a ha
    have := DFunLike.congr_fun h (Multiplicative.ofAdd ⟨a, ha⟩)
    simp only [ρ₀, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd] at this
    rw [hadd₂, hneg₂, this, inv_mul_cancel₀ (hB0 a y')]
  let ρ : G ⧸ Ap → (Multiplicative A →* L) := Quotient.lift ρ₀ fun y y' h => by

    have hq : (QuotientAddGroup.mk y : G ⧸ Ap) = QuotientAddGroup.mk y' := Quotient.sound h
    ext a
    simp only [ρ₀]
    rw [QuotientAddGroup.eq] at hq
    have := hq ((Multiplicative.toAdd a : A) : G) (Multiplicative.toAdd a).2
    rwa [hadd₂, hneg₂, inv_mul_eq_one₀ (hB0 _ y)] at this
  have hρ : Function.Injective ρ := by
    intro q q'
    induction q using Quotient.inductionOn with | h y => ?_
    induction q' using Quotient.inductionOn with | h y' => ?_
    intro h
    exact hρ₀ y y' h
  have := finite_monoidHom (Multiplicative A) L
  have := finite_monoidHom (Multiplicative (G ⧸ Ap)) L
  have ha : Nat.card (G ⧸ Ap) ≤ Nat.card A :=
    (Nat.card_le_card_of_injective ρ hρ).trans ((card_monoidHom_le (Multiplicative A) L).trans (by simp))

  let μ : App → (Multiplicative (G ⧸ Ap) →* L) := fun x =>
    { toFun := fun q => Quotient.lift (fun y : G => B (x : G) y)
          (fun y y' h => hwd x x.2 y y' (Quotient.sound h)) (Multiplicative.toAdd q)
      map_one' := by
        show Quotient.lift (fun y : G => B (x : G) y) _ (QuotientAddGroup.mk 0 : G ⧸ Ap) = 1
        exact hzero₂ x
      map_mul' := fun q q' => by
        induction q using Quotient.inductionOn with | h y => ?_
        induction q' using Quotient.inductionOn with | h y' => ?_
        exact hadd₂ (x : G) y y' }
  have hμ : Function.Injective μ := by
    intro x x' h
    apply Subtype.ext
    have hxy : ∀ y : G, B (x : G) y = B (x' : G) y := fun y =>
      DFunLike.congr_fun h (Multiplicative.ofAdd (QuotientAddGroup.mk y : G ⧸ Ap))
    apply sub_eq_zero.mp
    apply hleft
    intro y
    rw [sub_eq_add_neg, hadd₁, hneg₁, hxy, mul_inv_cancel₀ (hB0 _ y)]
  have hb : Nat.card App ≤ Nat.card (G ⧸ Ap) :=
    (Nat.card_le_card_of_injective μ hμ).trans ((card_monoidHom_le (Multiplicative (G ⧸ Ap)) L).trans (by simp))

  have hEq : A = App := AddSubgroup.eq_of_le_of_card_ge hAle (hb.trans ha)
  rwa [hEq]


-- created on 2026-10-09
