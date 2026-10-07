import Mathlib
import sympy.Basic

open IsLocalRing

/--
[CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CohCarrier_isUnit_index_of_forall_mem_iff_castHom_eq_one.lean)
-/
@[main]
private lemma main
  [CommRing 𝒪] [IsLocalRing 𝒪]
  {p : ℕ} [Fact p.Prime]
  {N r : ℕ} [NeZero N] [NeZero (N * r)]
  {H₀ : Subgroup (ZMod (N * r))ˣ}
-- given
  (hp𝒪 : (p : 𝒪) ∈ maximalIdeal 𝒪)
  (hr : r.Prime)
  (hr1 : ¬ p ∣ r - 1)
  (hH₀ : ∀ v : (ZMod (N * r))ˣ, v ∈ H₀ ↔ ZMod.castHom (dvd_mul_left r N) (ZMod r) (v : ZMod (N * r)) = 1) :
-- imply
  IsUnit ((H₀.index : ℕ) : 𝒪) := by
-- proof
  have : Fact r.Prime := ⟨hr⟩

  set f : (ZMod (N * r))ˣ →* (ZMod r)ˣ := ZMod.unitsMap (dvd_mul_left r N) with hf
  have hker : H₀ = f.ker := by
    ext v
    rw [hH₀, MonoidHom.mem_ker, ← Units.val_eq_one, hf, ZMod.unitsMap_def, Units.coe_map]
    rfl
  have hidx : H₀.index = r - 1 := by
    rw [hker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr (ZMod.unitsMap_surjective (dvd_mul_left r N)),
      Subgroup.card_top, Nat.card_eq_fintype_card, ZMod.card_units]
  rw [hidx]

  by_contra hnu
  have hmem : ((r - 1 : ℕ) : 𝒪) ∈ maximalIdeal 𝒪 := (mem_maximalIdeal _).mpr hnu
  have hcop : Nat.Coprime p (r - 1) := (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hr1
  have hcop' : IsCoprime (p : 𝒪) ((r - 1 : ℕ) : 𝒪) := by
    have := (Nat.isCoprime_iff_coprime.mpr hcop).map (Int.castRingHom 𝒪)
    simpa using this
  obtain ⟨a, b, hab⟩ := hcop'
  apply (maximalIdeal.isMaximal 𝒪).ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hp𝒪) (Ideal.mul_mem_left _ _ hmem)


-- created on 2026-10-05
