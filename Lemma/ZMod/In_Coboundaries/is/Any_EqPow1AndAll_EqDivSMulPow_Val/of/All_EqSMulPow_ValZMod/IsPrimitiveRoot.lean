import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.DualSelmer.ExtConditions
import Lemma.Int.P2MUtil

open CategoryTheory groupCohomology
open scoped IntermediateField Pointwise

/--
[groupCohomology_mem_coboundaries1_ofChar_iff_exists_rootOfUnity](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_mem_coboundaries1_ofChar_iff_exists_rootOfUnity.lean)
-/
@[path]
private lemma main
  {K L : Type} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime]
  {χ : (L ≃ₐ[K] L) →* (ZMod p)ˣ}
  {ζ : Lˣ}
  {c : (L ≃ₐ[K] L) → ZMod p}
-- given
  (hζp : IsPrimitiveRoot ζ p)
  (hζ : ∀ g : L ≃ₐ[K] L, g • ζ = ζ ^ (χ g : ZMod p).val) :
-- imply
  c ∈ coboundaries₁ (ofChar χ) ↔
      ∃ η : Lˣ, η ^ p = 1 ∧ ∀ g : L ≃ₐ[K] L, g • η / η = ζ ^ (c g).val := by
-- proof
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

  have key : ∀ (k : ℕ) (g : L ≃ₐ[K] L),
      (g • ζ ^ k / ζ ^ k = ζ ^ (c g).val ↔ (χ g : ZMod p) * k - k = c g) := by
    intro k g
    rw [smul_pow', hζ, ← pow_mul, div_eq_iff_eq_mul, ← pow_add, pow_eq_pow_iff_modEq, ← hζp.eq_orderOf,
      ← ZMod.natCast_eq_natCast_iff, Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val,
      ZMod.natCast_zmod_val, sub_eq_iff_eq_add]
  have hmem : c ∈ coboundaries₁ (ofChar χ) ↔ ∃ x : ZMod p, ∀ g, (χ g : ZMod p) * x - x = c g := by
    simp only [coboundaries₁, LinearMap.mem_range, funext_iff]
    exact ⟨fun ⟨x, hx⟩ => ⟨x, fun g => hx g⟩, fun ⟨x, hx⟩ => ⟨x, fun g => hx g⟩⟩
  rw [hmem]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨ζ ^ x.val, by rw [← pow_mul, mul_comm, pow_mul, hζp.pow_eq_one, one_pow], fun g => ?_⟩
    rw [key, ZMod.natCast_zmod_val]
    exact hx g
  · rintro ⟨η, hηp, hη⟩
    obtain ⟨k, -, hk⟩ := hζp.eq_pow_of_mem_rootsOfUnity (by rw [mem_rootsOfUnity]; exact hηp)
    exact ⟨(k : ZMod p), fun g => (key k g).mp (hk ▸ hη g)⟩


-- created on 2026-10-23
