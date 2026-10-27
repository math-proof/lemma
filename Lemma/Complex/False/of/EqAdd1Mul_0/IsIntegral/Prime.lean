import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GroupTheory.BurnsidePaqb.SimplePrime
open BurnsidePaqb


/--
[false_of_one_add_prime_mul_isIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
private lemma false_of_one_add_prime_mul_isIntegral
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
private lemma card_eq_prime_of_nontrivial_linear
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
    inferInstance
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
private lemma char_zero_of_nonlinear_of_coprime
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
  obtain hZ | h0 := burnside_coprime_vanish ρ g hcop
  · exfalso
    have hall := all_roots_eq_of_norm_eq ρ g hZ
    have hcard := charpoly_roots_card ρ g
    have hne0 : (ρ g).charpoly.roots ≠ 0 := by
      intro hz
      rw [hz, Multiset.card_zero] at hcard
      omega
    obtain ⟨μ₀, hμ₀⟩ := Multiset.exists_mem_of_ne_zero hne0
    have hμ : ∀ μ ∈ (ρ g).charpoly.roots, μ = μ₀ :=
      fun μ hμ => hall μ hμ μ₀ hμ₀
    have hsm := eq_smul_one_of_all_roots_eq ρ g μ₀ hμ
    have hgmem : g ∈ charCenter ρ := mem_charCenter_of_eq_smul ρ g μ₀ hsm
    have hproper : charCenter ρ ≠ ⊤ := charCenter_proper_of_nonlinear ρ hd
    have hbot : charCenter ρ = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (charCenter ρ)
        inferInstance with h | h
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
private lemma cor6_of_prime_pow_class
  [Group G] [Fintype G] [IsSimpleGroup G]
  {g : G}
-- given
  (hg1 : g ≠ 1)
  (hpp : IsPrimePow (conjClass g).card) :
-- imply
  ∃ r : ℕ, r.Prime ∧ Fintype.card G = r := by
-- proof
  classical
  obtain ⟨rr, kk, hrrP, hk0, hclass⟩ := hpp
  have hrr : rr.Prime := Nat.prime_iff.mpr hrrP
  by_cases hab : ∀ x y : G, x * y = y * x
  · let : CommGroup G := { ‹Group G› with mul_comm := hab }
    refine ⟨Fintype.card G, ?_, rfl⟩
    simpa only [Nat.card_eq_fintype_card] using
      (IsSimpleGroup.prime_card (α := G))
  · by_cases hlin : ∃ c : Irr G, c ≠ Irr.triv G ∧
    Module.finrank ℂ ↥(Irr.repBundle G c).1 = 1 ∧
    Representation.character
      ((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1)
      ≠ 1
    · obtain ⟨c, hc, hd1, hne⟩ := hlin
      have := (Irr.repBundle G c).2
      have hirr := irreducible_of_simple_fdrep G (Irr.repBundle G c).1
      have := hirr
      have : Nontrivial ↥(Irr.repBundle G c).1 :=
        IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) (Representation.asModule
          (((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1)))
      exact card_eq_prime_of_nontrivial_linear _ hd1 hne
    · exfalso
      have hterm : ∀ c : Irr G, c ≠ Irr.triv G →
        ∃ β : ℂ, IsIntegral ℤ β ∧
          Irr.charFun G c 1 * Irr.charFun G c g = (rr : ℂ) * β := by
        intro c hc
        have := (Irr.repBundle G c).2
        have hirr : Representation.IsIrreducible
          ((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1) :=
          irreducible_of_simple_fdrep G (Irr.repBundle G c).1
        have := hirr
        set ρc : Representation ℂ G ↥(Irr.repBundle G c).1 :=
          ((Irr.repBundle G c).1.ρ : Representation ℂ G ↥(Irr.repBundle G c).1)
          with hρc
        have : Nontrivial ↥(Irr.repBundle G c).1 :=
          IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρc.asModule
        have hchar : ∀ x, Irr.charFun G c x = ρc.character x :=
          fun x => Irr.charFun_eq_repBundle_char G c x
        have hdeg : Irr.charFun G c 1 =
          ((Module.finrank ℂ ↥(Irr.repBundle G c).1 : ℕ) : ℂ) :=
          Irr.charFun_one G c
        have hd : 1 ≤ Module.finrank ℂ ↥(Irr.repBundle G c).1 :=
          Module.finrank_pos
        by_cases hd1 : Module.finrank ℂ ↥(Irr.repBundle G c).1 = 1
        · have hch1 : ρc.character = 1 := by
          by_contra hne
          exact hlin ⟨c, hc, hd1, hne⟩
          exfalso
          apply hc
          have hfun : Irr.charFun G c = Irr.charFun G (Irr.triv G) := by
            funext x
            have e1 : Irr.charFun G c x = ρc.character x := hchar x
            have e2 : ρc.character x = 1 := by
              rw [hch1]
              exact Pi.one_apply x
            rw [e1, e2]
            exact (Irr.charFun_triv G x).symm
          exact Irr.charFun_inj G hfun
        · have hd2 : 1 < Module.finrank ℂ ↥(Irr.repBundle G c).1 := by omega
          by_cases hdiv : rr ∣ Module.finrank ℂ ↥(Irr.repBundle G c).1
          · refine ⟨((Module.finrank ℂ ↥(Irr.repBundle G c).1 / rr : ℕ) : ℂ) *
            Irr.charFun G c g, ?_, ?_⟩
            · rw [hchar g]
              exact (isIntegral_natCast _).mul (character_isIntegral _ _)
            · have hdm : rr * (Module.finrank ℂ ↥(Irr.repBundle G c).1 / rr)
              = Module.finrank ℂ ↥(Irr.repBundle G c).1 :=
              Nat.mul_div_cancel' hdiv
              have e1 : Irr.charFun G c 1 = (rr : ℂ) *
                ((Module.finrank ℂ ↥(Irr.repBundle G c).1 / rr : ℕ) : ℂ) := by
                rw [hdeg, ← Nat.cast_mul, hdm]
              rw [e1, hchar g]
              ring
          · have hcop : Nat.Coprime (conjClass g).card
            (Module.finrank ℂ ↥(Irr.repBundle G c).1) := by
            rw [← hclass]
            exact Nat.Coprime.pow_left kk ((hrr.coprime_iff_not_dvd).mpr hdiv)
            have hzero := char_zero_of_nonlinear_of_coprime ρc g hg1 hd2 hcop
            refine ⟨0, isIntegral_zero, ?_⟩
            rw [hchar g, hzero]
            simp
      have hsum := regular_character_vanishes G g hg1
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (Irr.triv G))] at hsum
      have htriv1 : Irr.charFun G (Irr.triv G) 1 * Irr.charFun G (Irr.triv G) g
        = 1 := by
        simp [Irr.charFun_triv]
      rw [htriv1] at hsum
      have hB : ∃ B : ℂ, IsIntegral ℤ B ∧
        ∑ c ∈ Finset.univ.erase (Irr.triv G),
          Irr.charFun G c 1 * Irr.charFun G c g = (rr : ℂ) * B := by
        have hch : ∀ c : Irr G, ∃ β : ℂ, (c ≠ Irr.triv G → IsIntegral ℤ β) ∧
          (c ≠ Irr.triv G → Irr.charFun G c 1 * Irr.charFun G c g
            = (rr : ℂ) * β) := by
          intro c
          by_cases hc : c = Irr.triv G
          · exact ⟨0, fun h => absurd hc h, fun h => absurd hc h⟩
          · obtain ⟨β, hβint, hβeq⟩ := hterm c hc
            exact ⟨β, fun _ => hβint, fun _ => hβeq⟩
        choose βf hβfint hβfeq using hch
        refine ⟨∑ c ∈ Finset.univ.erase (Irr.triv G), βf c, ?_, ?_⟩
        · exact IsIntegral.sum _
          (fun c hc => hβfint c (Finset.ne_of_mem_erase hc))
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl
            (fun c hc => hβfeq c (Finset.ne_of_mem_erase hc))
      obtain ⟨B, hBint, hBeq⟩ := hB
      rw [hBeq] at hsum
      exact false_of_one_add_prime_mul_isIntegral hrr hBint hsum

/--
[eq_smul_one_of_finrank_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/BurnsidePaqb/SimplePrime.lean)
-/
@[path]
private lemma eq_smul_one_of_finrank_one_eq
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
-- updated on 2026-10-26
