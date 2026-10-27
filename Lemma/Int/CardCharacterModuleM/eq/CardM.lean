import Mathlib
import Initialize.Tactic.Attr.Basic
open DirectSum


private lemma setOf_nsmul_eq_zero_addCircle (n : ℕ) (hn : n ≠ 0) :
  {a : AddCircle (1 : ℚ) | n • a = 0}
    = (AddSubgroup.zmultiples (((1 : ℚ) / n : ℚ) : AddCircle (1 : ℚ)) : Set (AddCircle (1 : ℚ))) := by
  ext a
  simp only [Set.mem_ofPred_eq, SetLike.mem_coe, AddSubgroup.mem_zmultiples_iff]
  constructor
  ·
    intro ha
    induction a using QuotientAddGroup.induction_on with
    | H x =>
      have h1 : ((n • x : ℚ) : AddCircle (1 : ℚ)) = 0 := by rwa [AddCircle.coe_nsmul]
      obtain ⟨k, hk⟩ := (AddCircle.coe_eq_zero_iff (p := (1 : ℚ)) (x := n • x)).1 h1
      refine ⟨k, ?_⟩
      rw [← AddCircle.coe_zsmul]
      congr 1
      rw [zsmul_eq_mul] at hk ⊢
      rw [nsmul_eq_mul, mul_one] at hk
      have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      field_simp
      linarith
  ·
    rintro ⟨k, rfl⟩
    rw [← natCast_zsmul, smul_smul, mul_comm, ← smul_smul, natCast_zsmul, ← AddCircle.coe_nsmul,
      nsmul_eq_mul]
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
    rw [mul_one_div_cancel hn', AddCircle.coe_period, smul_zero]

private lemma natCard_nsmul_eq_zero_addCircle (n : ℕ) (hn : n ≠ 0) :
  Nat.card {a : AddCircle (1 : ℚ) // n • a = 0} = n := by
  have h := setOf_nsmul_eq_zero_addCircle n hn
  have : Nat.card {a : AddCircle (1 : ℚ) // n • a = 0} =
    Nat.card (AddSubgroup.zmultiples (((1 : ℚ) / n : ℚ) : AddCircle (1 : ℚ))) := by
    show Nat.card ↥({a : AddCircle (1 : ℚ) | n • a = 0}) = _
    rw [h]; rfl
  rw [this, Nat.card_zmultiples, AddCircle.addOrderOf_period_div (Nat.pos_of_ne_zero hn)]

private lemma natCard_zmod_addMonoidHom_addCircle (n : ℕ) (hn : n ≠ 0) :
  Nat.card (ZMod n →+ AddCircle (1 : ℚ)) = n := by
  have e1 : (ZMod n →+ AddCircle (1 : ℚ)) ≃ {f : ℤ →+ AddCircle (1 : ℚ) // f n = 0} := (ZMod.lift n).symm
  have e2 : {f : ℤ →+ AddCircle (1 : ℚ) // f n = 0} ≃ {a : AddCircle (1 : ℚ) // n • a = 0} :=
    Equiv.subtypeEquiv (zmultiplesHom (AddCircle (1 : ℚ))).symm (fun f => by
      have hf : f (n : ℤ) = n • f 1 := by
        rw [show ((n : ℕ) : ℤ) = (n : ℤ) • (1 : ℤ) by simp, map_zsmul, natCast_zsmul]
      simp only [zmultiplesHom_symm_apply, hf])
  rw [Nat.card_congr (e1.trans e2), natCard_nsmul_eq_zero_addCircle n hn]

private lemma natCard_characterModule (M : Type*) [AddCommGroup M] [Finite M] :
  Nat.card (CharacterModule M) = Nat.card M := by
  classical
  obtain ⟨ι, hι, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' M
  have eC1 : CharacterModule M ≃ CharacterModule (⨁ i, ZMod (n i)) :=
    { toFun := fun φ => φ.comp e.symm.toAddMonoidHom
      invFun := fun ψ => ψ.comp e.toAddMonoidHom
      left_inv := fun φ => by ext x; show φ (e.symm (e x)) = φ x; rw [e.symm_apply_apply]
      right_inv := fun ψ => by ext x; show ψ (e (e.symm x)) = ψ x; rw [e.apply_symm_apply] }
  have eC2 : CharacterModule (⨁ i, ZMod (n i)) ≃ (Π i, ZMod (n i) →+ AddCircle (1 : ℚ)) :=
    (DFinsupp.liftAddHom (β := fun i => ZMod (n i)) (γ := AddCircle (1 : ℚ))).symm.toEquiv
  have eM : M ≃ (Π i, ZMod (n i)) := e.toEquiv.trans (DFinsupp.equivFunOnFintype (β := fun i => ZMod (n i)))
  rw [Nat.card_congr (eC1.trans eC2), Nat.card_congr eM, Nat.card_pi, Nat.card_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [natCard_zmod_addMonoidHom_addCircle (n i) (by have := hn i; omega), Nat.card_zmod]
/--
[CharacterModule_natCard_eq_of_finite](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CharacterModule_natCard_eq_of_finite.lean)
-/
@[path]
private lemma main
  [AddCommGroup M] [Finite M] :
-- imply
  Nat.card (CharacterModule M) = Nat.card M :=
-- proof
  natCard_characterModule M


-- created on 2026-10-23
