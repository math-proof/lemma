module
public import Mathlib
public import Initialize.Tactic.Attr.Basic
public import Def.GroupTheory.BurnsidePaqb.SimplePrime
open BurnsidePaqb
set_option linter.style.haveILetI false in


public section

/--
[false_of_one_add_prime_mul_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
theorem false_of_one_add_prime_mul_isIntegral
  [Group G] [Fintype G]
  {p : ℕ}
  {β : ℂ}
-- given
  (hp : p.Prime)
  (hβ : IsIntegral ℤ β)
  (h : 1 + (p : ℂ) * β = 0) :
-- imply
  False := by
-- proof
  have hβeq : β = -1 / (p : ℂ) := by
    have hp0 : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have h1 : (p : ℂ) * β = -1 := eq_neg_of_add_eq_zero_right h
    rwa [eq_div_iff hp0, mul_comm]
  have hβq : IsIntegral ℤ (-1 / (p : ℚ)) := by
    haveI : IsScalarTower ℤ ℚ ℂ := IsScalarTower.of_algebraMap_eq fun x => by simp
    have hiff :=
      isIntegral_algebraMap_iff (R := ℤ) (A := ℚ) (B := ℂ) (x := -1 / (p : ℚ))
    apply hiff.mp
    have e : algebraMap ℚ ℂ (-1 / (p : ℚ)) = β := by
      rw [eq_ratCast, hβeq]
      push_cast
      ring
    rwa [e]
  have : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  obtain ⟨n, hn⟩ := (isIntegrallyClosed_iff ℚ).mp inferInstance hβq
  have hcast : (n : ℚ) = -1 / (p : ℚ) := by simpa using hn
  have hpn : (p : ℚ) * n = -1 := by
    have hp0 : ((p : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
    rw [hcast]
    field_simp
  have hzz : (p : ℤ) * n = -1 := by exact_mod_cast hpn
  have hdvd : (p : ℤ) ∣ 1 := ⟨-n, by rw [mul_neg, hzz]; simp⟩
  have hdvdN : p ∣ 1 := by exact_mod_cast hdvd
  exact hp.not_dvd_one hdvdN

/--
[card_eq_prime_of_nontrivial_linear](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
theorem card_eq_prime_of_nontrivial_linear
  [Group G] [Fintype G] [IsSimpleGroup G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V}
-- given
  (hd : Module.finrank ℂ V = 1)
  (hne : ρ.character ≠ 1) :
-- imply
  ∃ r : ℕ, r.Prime ∧ Fintype.card G = r := by
-- proof
  set lam : G →* ℂˣ := linearCharHom ρ hd with hlamdef
  have hchar : ∀ g : G, ρ.character g = (lam g : ℂ) := fun g => rfl
  have hker_ne_top : lam.ker ≠ ⊤ := by
    intro hcon
    apply hne
    funext g
    have hg : g ∈ lam.ker := hcon ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at hg
    rw [hchar g]
    have h1 : ((1 : ℂˣ) : ℂ) = 1 := Units.val_one
    rwa [hg]
  have hker_cases := IsSimpleGroup.eq_bot_or_eq_top_of_normal lam.ker
  obtain hbot | htop := hker_cases
  · have hinj : Function.Injective lam :=
    (MonoidHom.ker_eq_bot_iff lam).mp hbot
    have hcomm : ∀ x y : G, x * y = y * x := fun x y =>
      hinj (by simp [map_mul, mul_comm])
    let : CommGroup G := { ‹Group G› with mul_comm := hcomm }
    refine ⟨Fintype.card G, ?_, rfl⟩
    simpa only [Nat.card_eq_fintype_card] using
      (IsSimpleGroup.prime_card (α := G))
  · exact absurd htop hker_ne_top

/--
[char_zero_of_nonlinear_of_coprime](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
theorem char_zero_of_nonlinear_of_coprime
  [Group G] [Fintype G] [IsSimpleGroup G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [Nontrivial V]
  {ρ : Representation ℂ G V} [Representation.IsIrreducible ρ]
  {g : G}
-- given
  (hne1 : g ≠ 1)
  (hd : 1 < Module.finrank ℂ V)
  (hcop : Nat.Coprime (conjClass g).card (Module.finrank ℂ V)) :
-- imply
  ρ.character g = 0 := by
-- proof
  obtain hZ | h0 := burnside_coprime_vanish (ρ := ρ) (g := g) hcop
  · exfalso
    have hall := all_roots_eq_of_norm_eq (ρ := ρ) (g := g) hZ
    have hcard := charpoly_roots_card (ρ := ρ) (g := g)
    have hne0 : (ρ g).charpoly.roots ≠ 0 := by
      intro hz
      rw [hz, Multiset.card_zero] at hcard
      omega
    obtain ⟨μ₀, hμ₀⟩ := Multiset.exists_mem_of_ne_zero hne0
    have hμ : ∀ μ ∈ (ρ g).charpoly.roots, μ = μ₀ :=
      fun μ hμ => hall μ hμ μ₀ hμ₀
    have hsm := eq_smul_one_of_all_roots_eq (ρ := ρ) (g := g) (μ₀ := μ₀) hμ
    have hgmem : g ∈ charCenter ρ :=
      mem_charCenter_of_eq_smul (ρ := ρ) (g := g) (c := μ₀) hsm
    have hproper : charCenter ρ ≠ ⊤ := charCenter_proper_of_nonlinear (ρ := ρ) hd
    have hbot : charCenter ρ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (charCenter ρ) with h | h
      · exact h
      · exact absurd h hproper
    have hmem : g ∈ (⊥ : Subgroup G) := hbot ▸ hgmem
    rw [Subgroup.mem_bot] at hmem
    exact hne1 hmem
  · exact h0

/--
[cor6_of_prime_pow_class](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
theorem cor6_of_prime_pow_class
  [Group G] [Fintype G] [IsSimpleGroup G]
  {g : G}
-- given
  (hg1 : g ≠ 1)
  (hpp : IsPrimePow (conjClass g).card) :
-- imply
  ∃ r : ℕ, r.Prime ∧ Fintype.card G = r := by
-- proof
  -- Upstream proves this with the character-orthogonality API
  -- (`Irr.charFun_triv`, `Irr.charFun_inj`, `Irr.charFun_one`,
  -- `Irr.charFun_eq_repBundle_char`, `regular_character_vanishes`,
  -- `irreducible_of_simple_fdrep`), none of which is ported in this repository.
  -- Upstream keeps the corresponding development as `sorry` as well.
  sorry

/--
[eq_smul_one_of_finrank_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
theorem eq_smul_one_of_finrank_one_eq
  [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  {ρ : Representation ℂ G V}
  {g : G}
-- given
  (hd : Module.finrank ℂ V = 1) :
-- imply
  ρ g = ρ.character g • 1 := by
-- proof
  apply BurnsidePaqb.eq_smul_one_of_finrank_one ρ hd g


-- created on 2026-10-20
-- updated on 2026-11-23
