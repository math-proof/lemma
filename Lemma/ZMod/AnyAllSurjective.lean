import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma exists_surjective_of_dvd_card
  (G : Type*) [CommGroup G] [Finite G] [hG : IsCyclic G]
  (n : ℕ) [NeZero n] (hn : n ∣ Nat.card G) :
  ∃ f : G →* Multiplicative (ZMod n), Function.Surjective f := by
  let e : G ≃* Multiplicative (ZMod (Nat.card G)) := (zmodCyclicMulEquiv hG).symm
  let r : Multiplicative (ZMod (Nat.card G)) →* Multiplicative (ZMod n) :=
    AddMonoidHom.toMultiplicative (ZMod.castHom hn (ZMod n)).toAddMonoidHom
  refine ⟨r.comp e.toMonoidHom, ?_⟩
  have hr : Function.Surjective r := by
    intro y
    refine ⟨Multiplicative.ofAdd (((Multiplicative.toAdd y).val : ℕ) : ZMod (Nat.card G)), ?_⟩
    show Multiplicative.ofAdd (ZMod.castHom hn (ZMod n) (((Multiplicative.toAdd y).val : ℕ) : ZMod (Nat.card G))) = y
    rw [map_natCast, ZMod.natCast_zmod_val]
    rfl
  refine hr.comp e.surjective
private noncomputable def piDelta
  (p : ℕ) [Fact p.Prime] (q : ℕ) :
  Units (ZMod q) →* Multiplicative (ZMod (p ^ padicValNat p (q - 1))) :=
  if h : q.Prime ∧ (p ^ padicValNat p (q - 1) ∣ Nat.card (Units (ZMod q))) then
    let _ : Fact q.Prime := ⟨h.1⟩
    (exists_surjective_of_dvd_card (Units (ZMod q)) (p ^ padicValNat p (q - 1)) h.2).choose
  else 1
private lemma helper_main
  (p : ℕ) [Fact p.Prime] :
  ∃ πΔ : (q : ℕ) → (Units (ZMod q) →* Multiplicative (ZMod (p ^ padicValNat p (q - 1)))),
    ∀ q : ℕ, q.Prime → q ≠ p → Function.Surjective (πΔ q) := by
  refine ⟨piDelta p, fun q hq _ => ?_⟩
  let _ : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (Units (ZMod q)) = q - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hdvd : p ^ padicValNat p (q - 1) ∣ Nat.card (Units (ZMod q)) := by
    rw [hcard]
    refine pow_padicValNat_dvd
  have h : q.Prime ∧ (p ^ padicValNat p (q - 1) ∣ Nat.card (Units (ZMod q))) := ⟨hq, hdvd⟩
  unfold piDelta
  rw [dite_eq_left h]
  refine (exists_surjective_of_dvd_card (Units (ZMod q)) (p ^ padicValNat p (q - 1)) h.2).choose_spec
/--
[ZMod_exists_surjective_units_to_multiplicative_padic_family](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ZMod_exists_surjective_units_to_multiplicative_padic_family.lean)
-/
@[path]
private lemma main
  (p : ℕ) [Fact p.Prime] :
  -- imply
  ∃ πΔ : (q : ℕ) → (Units (ZMod q) →* Multiplicative (ZMod (p ^ padicValNat p (q - 1)))),
    ∀ q : ℕ, q.Prime → q ≠ p → Function.Surjective (πΔ q) :=
  helper_main p


-- created on 2026-10-20
