import Mathlib
import sympy.Basic

open scoped Classical

/--
[AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AddMonoidHom_natCard_ker_eq_natCard_ker_of_pairing_adjoint.lean)
-/

private lemma e_zero_left
  {P : Type*}
  [AddCommGroup P]
  [Finite P]
  {K : Type*}
  [Field K]
  (e : P → P → Kˣ)
  (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
  (y : P) : e 0 y = 1 := by
  have h := hadd₁ 0 0 y
  rw [add_zero] at h
  exact (mul_eq_left.mp h.symm)

private lemma e_zero_right
  {P : Type*}
  [AddCommGroup P]
  [Finite P]
  {K : Type*}
  [Field K]
  (e : P → P → Kˣ)
  (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
  (x : P) : e x 0 = 1 := by
  have h := hadd₂ x 0 0
  rw [add_zero] at h
  exact (mul_eq_right.mp h.symm)

private lemma e_neg_left
  {P : Type*}
  [AddCommGroup P]
  [Finite P]
  {K : Type*}
  [Field K]
  (e : P → P → Kˣ)
  (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
  (x y : P) : e (-x) y = (e x y)⁻¹ := by
  have h := hadd₁ (-x) x y
  rw [neg_add_cancel, e_zero_left e hadd₁] at h
  exact eq_inv_of_mul_eq_one_left h.symm

private lemma e_sub_left
  {P : Type*}
  [AddCommGroup P]
  [Finite P]
  {K : Type*}
  [Field K]
  (e : P → P → Kˣ)
  (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
  (x x' y : P) : e (x - x') y = e x y * (e x' y)⁻¹ := by
  rw [sub_eq_add_neg, hadd₁, e_neg_left e hadd₁]

def chR
  {P : Type*}
  [AddCommGroup P]
  [Finite P]
  {K : Type*}
  [Field K]
  (e : P → P → Kˣ)
  (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
  (y : P) : Multiplicative P →* Kˣ where
  toFun := fun x => e (Multiplicative.toAdd x) y
  map_one' := e_zero_left e hadd₁ y
  map_mul' := fun _ _ => hadd₁ _ _ _

def annR
  {P : Type*}
  [AddCommGroup P]
  [Finite P]
  {K : Type*}
  [Field K]
  (e : P → P → Kˣ)
  (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
  (S : AddSubgroup P) : AddSubgroup P where
  carrier := {y | ∀ s ∈ S, e s y = 1}
  zero_mem' := fun s _ => e_zero_right e hadd₂ s
  add_mem' := by
    intro a b ha hb s hs
    show e s (a + b) = 1
    rw [hadd₂, ha s hs, hb s hs, one_mul]
  neg_mem' := by
    intro a ha s hs
    show e s (-a) = 1
    have h := hadd₂ s (-a) a
    rw [neg_add_cancel, e_zero_right e hadd₂, ha s hs, mul_one] at h
    rw [← h]

@[simp] lemma chR_apply
  {P : Type*}
  [AddCommGroup P]
  [Finite P]
  {K : Type*}
  [Field K]
  (e : P → P → Kˣ)
  (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
  (y : P) (x : Multiplicative P) : chR e hadd₁ y x = e (Multiplicative.toAdd x) y := rfl

private lemma mem_annR
  {P : Type*}
  [AddCommGroup P]
  [Finite P]
  {K : Type*}
  [Field K]
  (e : P → P → Kˣ)
  (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
  {S : AddSubgroup P} {y : P} : y ∈ annR e hadd₂ S ↔ ∀ s ∈ S, e s y = 1 := Iff.rfl

private lemma natCard_monoidHom_units_le (G : Type*) [CommGroup G] [Finite G] (K : Type*) [Field K] :
  Nat.card (G →* Kˣ) ≤ Nat.card G := by
  classical
  have := Fintype.ofFinite G
  have := Fintype.ofFinite (G →* Kˣ)

  let ι : (G →* Kˣ) → (G →* K) := fun χ => (Units.coeHom K).comp χ
  have hι : Function.Injective ι := by
    intro χ χ' h; ext g
    exact DFunLike.congr_fun h g
  have hli : LinearIndependent K (fun χ : G →* Kˣ => ((ι χ : G →* K) : G → K)) :=
    (linearIndependent_monoidHom G K).comp ι hι
  have h1 := hli.fintype_card_le_finrank
  rwa [Module.finrank_pi K, Fintype.card_eq_nat_card, Fintype.card_eq_nat_card] at h1

private lemma natCard_annR_mul_natCard
  {P : Type*}
  [AddCommGroup P]
  [Finite P]
  {K : Type*}
  [Field K]
  (e : P → P → Kˣ)
  (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
  (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
  (hleft : ∀ x, (∀ y, e x y = 1) → x = 0) (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
  (hsurj : ∀ χ : Multiplicative P →* Kˣ, ∃ y, ∀ x, e x y = χ (Multiplicative.ofAdd x))
  (S : AddSubgroup P) :
    Nat.card (annR e hadd₂ S) * Nat.card S = Nat.card P := by
  classical

  let incl : Multiplicative S →* Multiplicative P := AddMonoidHom.toMultiplicative S.subtype
  let ρ : (Multiplicative P →* Kˣ) →* (Multiplicative S →* Kˣ) :=
    { toFun := fun χ => χ.comp incl
      map_one' := by ext; rfl
      map_mul' := fun _ _ => by ext; rfl }

  have hbij : Function.Bijective (chR e hadd₁) := by
    constructor
    ·
      intro y y' h
      apply sub_eq_zero.mp
      apply hright
      intro x
      have hx := DFunLike.congr_fun h (Multiplicative.ofAdd x)
      simp only [chR_apply, toAdd_ofAdd] at hx
      have h2 := hadd₂ x (y - y') y'
      rw [sub_add_cancel, hx] at h2
      exact (mul_eq_right.mp h2.symm)
    ·
      intro χ
      obtain ⟨y, hy⟩ := hsurj χ
      exact ⟨y, MonoidHom.ext fun x => by rw [chR_apply, hy]; rfl⟩
  have hcardHom : Nat.card (Multiplicative P →* Kˣ) = Nat.card P :=
    (Nat.card_eq_of_bijective _ hbij).symm

  have hker : Nat.card ρ.ker = Nat.card (annR e hadd₂ S) := by
    refine (Nat.card_eq_of_bijective
      (fun y : annR e hadd₂ S => (⟨chR e hadd₁ y.1, ?_⟩ : ρ.ker)) ⟨?_, ?_⟩).symm
    ·
      rw [MonoidHom.mem_ker]
      refine MonoidHom.ext fun s => ?_
      show e (Multiplicative.toAdd (incl s)) y.1 = 1
      exact y.2 _ (by show ((S.subtype) (Multiplicative.toAdd s) : P) ∈ S; exact (Multiplicative.toAdd s).2)
    ·
      intro y y' h
      exact Subtype.ext (hbij.1 (congrArg (fun z : ρ.ker => (z : Multiplicative P →* Kˣ)) h))
    ·
      rintro ⟨χ, hχ⟩
      obtain ⟨y, rfl⟩ := hbij.2 χ
      refine ⟨⟨y, fun s hs => ?_⟩, rfl⟩
      have := DFunLike.congr_fun (MonoidHom.mem_ker.mp hχ) (Multiplicative.ofAdd ⟨s, hs⟩)
      exact this

  have hle1 : Nat.card ρ.range ≤ Nat.card S := by
    refine (Nat.card_le_card_of_injective (fun χ : ρ.range => (χ : Multiplicative S →* Kˣ))
      Subtype.val_injective).trans ?_
    have h__af := natCard_monoidHom_units_le (Multiplicative S) K
    simp at h__af ⊢
    exact h__af
  have hle2 : Nat.card S ≤ Nat.card ρ.range := by
    let ev : Multiplicative S → (ρ.range →* Kˣ) := fun s =>
      { toFun := fun χ => (χ : Multiplicative S →* Kˣ) s
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hev : Function.Injective ev := by
      intro s s' h
      have key : ∀ y : P,
        e (S.subtype (Multiplicative.toAdd s)) y = e (S.subtype (Multiplicative.toAdd s')) y := by
        intro y
        have := DFunLike.congr_fun h ⟨ρ (chR e hadd₁ y), ⟨_, rfl⟩⟩
        exact this
      have hzero :
        (S.subtype (Multiplicative.toAdd s) : P) - S.subtype (Multiplicative.toAdd s') = 0 :=
        hleft _ fun y => by rw [e_sub_left e hadd₁, key y, mul_inv_cancel]
      have : Multiplicative.toAdd s = Multiplicative.toAdd s' :=
        S.subtype_injective (sub_eq_zero.mp hzero)
      exact Multiplicative.toAdd.injective this
    calc _ = Nat.card (Multiplicative S) := Nat.card_congr Multiplicative.toAdd.symm
      _ ≤ Nat.card (ρ.range →* Kˣ) := Nat.card_le_card_of_injective ev hev
      _ ≤ Nat.card ρ.range := natCard_monoidHom_units_le _ K
  have hrange : Nat.card ρ.range = Nat.card S := le_antisymm hle1 hle2

  have hexact : Nat.card (Multiplicative P →* Kˣ) = Nat.card ρ.ker * Nat.card ρ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
  rw [← hcardHom, hexact, hker, hrange]

@[main]
private lemma main
  [AddCommGroup P] [Finite P] [Field K]
  {e : P → P → Kˣ}
  {T T' : P →+ P}
-- given
  (hadd₁ : ∀ x x' y, e (x + x') y = e x y * e x' y)
  (hadd₂ : ∀ x y y', e x (y + y') = e x y * e x y')
  (hleft : ∀ x, (∀ y, e x y = 1) → x = 0)
  (hright : ∀ y, (∀ x, e x y = 1) → y = 0)
  (hsurj : ∀ χ : Multiplicative P →* Kˣ, ∃ y, ∀ x, e x y = χ (Multiplicative.ofAdd x))
  (hadj : ∀ x y, e (T x) y = e x (T' y)) :
-- imply
  Nat.card (T.ker) = Nat.card (T'.ker) := by
-- proof
  classical

  have hkerT' : ∀ y, y ∈ T'.ker ↔ y ∈ annR e hadd₂ T.range := by
    intro y
    rw [AddMonoidHom.mem_ker, mem_annR]
    constructor
    ·
      rintro h _ ⟨x, rfl⟩
      rw [hadj, h, e_zero_right e hadd₂]
    ·
      intro h
      apply hright
      intro x
      rw [← hadj]
      exact h _ ⟨x, rfl⟩
  have hEq : T'.ker = annR e hadd₂ T.range := AddSubgroup.ext hkerT'

  have h1 := natCard_annR_mul_natCard e hadd₁ hadd₂ hleft hright hsurj T.range
  have h2 : Nat.card T.ker * Nat.card T.range = Nat.card P := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup T.ker, mul_comm,
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange T).toEquiv]
  have hpos : 0 < Nat.card T.range := Nat.card_pos
  rw [hEq]
  exact Nat.eq_of_mul_eq_mul_right hpos (h2.trans h1.symm)


-- created on 2026-10-09
