import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma exists_inv_mem {F : Type u} [Field F] (O : ValuationSubring F) {Kbar : Type u} [Field Kbar] (res : O →+* Kbar) (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res) (x : F) (hx : x ∈ O) (h0 : res ⟨x, hx⟩ ≠ 0) : ∃ hx' : x⁻¹ ∈ O, res ⟨x⁻¹, hx'⟩ = (res ⟨x, hx⟩)⁻¹ := by
  have hu : IsUnit (⟨x, hx⟩ : O) := by
    by_contra h
    apply h0 (hker ((IsLocalRing.mem_maximalIdeal _).mpr h))
  obtain ⟨u, hu⟩ := hu
  have hx0 : x ≠ 0 := by
    intro h
    subst h
    apply h0
    have : (⟨(0 : F), hx⟩ : O) = 0 := rfl
    rw [this, map_zero]
  have hinv : ((u⁻¹ : Units O) : O) = (x⁻¹ : F) := by
    have h1 : ((u⁻¹ : Units O) : O) * (u : O) = 1 := u.inv_mul
    apply eq_inv_of_mul_eq_one_left
    have := congrArg (fun y : O => (y : F)) h1
    simpa [hu] using this
  refine ⟨hinv ▸ ((u⁻¹ : Units O) : O).2, ?_⟩
  have h3 : (⟨x⁻¹, hinv ▸ ((u⁻¹ : Units O) : O).2⟩ : O) = ((u⁻¹ : Units O) : O) := Subtype.ext hinv.symm
  rw [h3, map_units_inv, hu]
private lemma apply_eq_zero_of_not_isUnit {F : Type u} [Field F] (O : ValuationSubring F) {Kbar : Type u} [Field Kbar] (res : O →+* Kbar) (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res) (x : O) (hx : ¬IsUnit x) : res x = 0 := hker ((IsLocalRing.mem_maximalIdeal _).mpr hx)
private noncomputable def composite {F : Type u} [Field F] (O : ValuationSubring F) {Kbar : Type u} [Field Kbar] (res : O →+* Kbar) (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res) (W : ValuationSubring Kbar) : ValuationSubring F where
  carrier := {x | ∃ hx : x ∈ O, res ⟨x, hx⟩ ∈ W}
  mul_mem' := by
    intro a b hapair hbpair
    obtain ⟨ha, haW⟩ := hapair
    obtain ⟨hb, hbW⟩ := hbpair
    refine ⟨MulMemClass.mul_mem ha hb, ?_⟩
    have : (⟨a * b, MulMemClass.mul_mem ha hb⟩ : O) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, map_mul]
    apply MulMemClass.mul_mem haW hbW
  one_mem' := ⟨O.one_mem, by
    have : (⟨(1 : F), O.one_mem⟩ : O) = 1 := rfl
    rw [this, map_one]
    apply W.one_mem⟩
  add_mem' := by
    intro a b hapair hbpair
    obtain ⟨ha, haW⟩ := hapair
    obtain ⟨hb, hbW⟩ := hbpair
    refine ⟨AddMemClass.add_mem ha hb, ?_⟩
    have : (⟨a + b, AddMemClass.add_mem ha hb⟩ : O) = ⟨a, ha⟩ + ⟨b, hb⟩ := rfl
    rw [this, map_add]
    apply AddMemClass.add_mem haW hbW
  zero_mem' := ⟨O.zero_mem, by
    have : (⟨(0 : F), O.zero_mem⟩ : O) = 0 := rfl
    rw [this, map_zero]
    apply W.zero_mem⟩
  neg_mem' := by
    intro a hapair
    obtain ⟨ha, haW⟩ := hapair
    refine ⟨NegMemClass.neg_mem ha, ?_⟩
    have : (⟨-a, NegMemClass.neg_mem ha⟩ : O) = -⟨a, ha⟩ := rfl
    rw [this, map_neg]
    apply NegMemClass.neg_mem haW
  mem_or_inv_mem' := by
    intro x
    if hx : x ∈ O then
      if hW : res ⟨x, hx⟩ ∈ W then
        exact Or.inl ⟨hx, hW⟩
      else
        right
        have h0 : res ⟨x, hx⟩ ≠ 0 := by
          intro h
          apply hW (h ▸ W.zero_mem)
        obtain ⟨hx', hres⟩ := exists_inv_mem O res hker x hx h0
        refine ⟨hx', ?_⟩
        rw [hres]
        obtain h | h := W.mem_or_inv_mem (res ⟨x, hx⟩)
        · apply (hW h).elim
        · apply h
    else
      right
      have hx' : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hx
      refine ⟨hx', ?_⟩
      have hnu : ¬IsUnit (⟨x⁻¹, hx'⟩ : O) := by
        intro hu
        have h0 : res ⟨x⁻¹, hx'⟩ ≠ 0 := (hu.map res).ne_zero
        obtain ⟨hx'', _⟩ := exists_inv_mem O res hker x⁻¹ hx' h0
        apply hx (by simpa using hx'')
      rw [apply_eq_zero_of_not_isUnit O res hker _ hnu]
      apply W.zero_mem
private lemma mem_composite_iff {F : Type u} [Field F] (O : ValuationSubring F) {Kbar : Type u} [Field Kbar] (res : O →+* Kbar) (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res) (W : ValuationSubring Kbar) {x : F} : x ∈ composite O res hker W ↔ ∃ hx : x ∈ O, res ⟨x, hx⟩ ∈ W := Iff.rfl
private lemma composite_le {F : Type u} [Field F] (O : ValuationSubring F) {Kbar : Type u} [Field Kbar] (res : O →+* Kbar) (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res) (W : ValuationSubring Kbar) : composite O res hker W ≤ O := by
  intro x hxpair
  obtain ⟨hx, _⟩ := hxpair
  apply hx
private lemma coe_mem_composite_iff {F : Type u} [Field F] (O : ValuationSubring F) {Kbar : Type u} [Field Kbar] (res : O →+* Kbar) (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res) (W : ValuationSubring Kbar) (x : O) : (x : F) ∈ composite O res hker W ↔ res x ∈ W := by
  rw [mem_composite_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨x.2, h⟩⟩
private lemma coe_mem_nonunits_composite_iff {F : Type u} [Field F] (O : ValuationSubring F) {Kbar : Type u} [Field Kbar] (res : O →+* Kbar) (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res) (W : ValuationSubring Kbar) (x : O) : (x : F) ∈ (composite O res hker W).nonunits ↔ res x ∈ W.nonunits := by
  rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_nonunits_iff_or]
  constructor
  ·
    intro hmem
    obtain h | h := hmem
    ·
      left
      have : x = 0 := Subtype.ext h
      rw [this, map_zero]
    ·
      if h0 : res x = 0 then
        apply Or.inl h0
      else
        right
        intro hW
        obtain ⟨hx', hres⟩ := exists_inv_mem O res hker (x : F) x.2 (by simpa using h0)
        apply h
        rw [mem_composite_iff]
        refine ⟨hx', ?_⟩
        rw [hres]
        simpa using hW
  ·
    intro hmem
    obtain h | h := hmem
    ·
      if hx0 : (x : F) = 0 then
        apply Or.inl hx0
      else
        right
        intro hmem
        have hxO : (x : F)⁻¹ ∈ O := composite_le O res hker W hmem
        have hu : IsUnit x := by
          refine isUnit_iff_exists_inv.mpr ⟨⟨(x : F)⁻¹, hxO⟩, ?_⟩
          apply Subtype.ext
          simp [hx0]
        refine ((hu.map res).ne_zero h).elim
    ·
      right
      intro hmem
      apply h
      have hxO : (x : F)⁻¹ ∈ O := composite_le O res hker W hmem
      have hx0 : (x : F) ≠ 0 := by
        intro e
        apply h
        have : x = 0 := Subtype.ext e
        rw [this, map_zero, inv_zero]
        apply W.zero_mem
      have h0 : res x ≠ 0 := by
        have hu : IsUnit x := by
          refine isUnit_iff_exists_inv.mpr ⟨⟨(x : F)⁻¹, hxO⟩, ?_⟩
          apply Subtype.ext
          simp [hx0]
        refine (hu.map res).ne_zero
      obtain ⟨hx', hres⟩ := exists_inv_mem O res hker (x : F) x.2 (by simpa using h0)
      have := (coe_mem_composite_iff O res hker W ⟨(x : F)⁻¹, hx'⟩).mp hmem
      rw [hres] at this
      simpa using this
/--
[ValuationSubring_exists_le_forall_mem_iff_apply_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_le_forall_mem_iff_apply_mem.lean)
-/
@[path]
private lemma main
  {F : Type u} [Field F]
  {Kbar : Type u} [Field Kbar]
  (O : ValuationSubring F)
  (res : O →+* Kbar)
  (W : ValuationSubring Kbar)
  -- given
  (hker : IsLocalRing.maximalIdeal O ≤ RingHom.ker res) :
  -- imply
  ∃ O' : ValuationSubring F, O' ≤ O ∧ (∀ x : O, (x : F) ∈ O' ↔ res x ∈ W) ∧ (∀ x : O, (x : F) ∈ O'.nonunits ↔ res x ∈ W.nonunits) :=
  ⟨composite O res hker W, composite_le O res hker W, coe_mem_composite_iff O res hker W, coe_mem_nonunits_composite_iff O res hker W⟩


-- created on 2026-10-20
