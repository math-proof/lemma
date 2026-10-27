import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private noncomputable def sUnit
  (q : ℕ) [Fact q.Prime] (c : (ZMod q)ˣ) : (GaloisField q 2)ˣ :=
  Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c

private lemma sUnit_normUnit
  {q : ℕ} [Fact q.Prime]
  (β : (GaloisField q 2)ˣ) :
  -- imply
  sUnit q (Units.map (Algebra.norm (ZMod q) (S := GaloisField q 2)) β) = β ^ (q + 1) := by
  -- proof
  have hexp : (Nat.card (GaloisField q 2) - 1) / (Nat.card (ZMod q) - 1) = q + 1 := by
    rw [GaloisField.card q 2 two_ne_zero, Nat.card_zmod]
    have hq : 1 < q := (Fact.out : q.Prime).one_lt
    have hmul : q ^ 2 - 1 = (q + 1) * (q - 1) := by
      have h1 : 1 ≤ q := hq.le
      have h2 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1, h2]
      ring
    rw [hmul, Nat.mul_div_cancel _ (by omega)]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val]
  change algebraMap (ZMod q) (GaloisField q 2) (Algebra.norm (ZMod q) (β : GaloisField q 2)) = (β : GaloisField q 2) ^ (q + 1)
  rw [FiniteField.algebraMap_norm_eq_pow, hexp]

/--
[CuspidalType_pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CuspidalType_pow_add_one_eq_one_iff_forall_theta_scalarUnit_eq_one.lean)
-/
@[path]
private lemma main
  {q : ℕ} [Fact q.Prime]
  {K : Type u} [Field K]
  (θ : (GaloisField q 2)ˣ →* Kˣ) :
  -- imply
  θ ^ (q + 1) = 1 ↔ ∀ c : (ZMod q)ˣ, θ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1 := by
  -- proof
  constructor
  ·
    intro hθ c
    change θ (sUnit q c) = 1
    obtain ⟨β, hβ⟩ := FiniteField.unitsMap_norm_surjective (ZMod q) (GaloisField q 2) c
    rw [← hβ, sUnit_normUnit, map_pow, ← MonoidHom.pow_apply, hθ, MonoidHom.one_apply]
  ·
    intro hθ
    ext β
    rw [MonoidHom.pow_apply, ← map_pow, ← sUnit_normUnit, MonoidHom.one_apply]
    apply congrArg Units.val (hθ (Units.map (Algebra.norm (ZMod q) (S := GaloisField q 2)) β))


-- created on 2026-10-20
