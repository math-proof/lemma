import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma Submodule.eq_top_of_card_eq' {R : Type*} [Semiring R] {V : Type*}
    [AddCommGroup V] [Module R V] [Finite V] {N : Submodule R V}
    (h : Nat.card ↥N = Nat.card V) : N = ⊤ := by
  rw [eq_top_iff]; intro x _
  have hbij := N.subtype_injective.bijective_of_nat_card_le (by rw [h])
  obtain ⟨⟨y, hy⟩, hy'⟩ := hbij.2 x
  exact hy' ▸ hy
private lemma Submodule.eq_of_le_of_card_eq' {R : Type*} [Semiring R] {V : Type*}
    [AddCommGroup V] [Module R V] [Finite V] {K L : Submodule R V}
    (hle : K ≤ L) (hc : Nat.card ↥K = Nat.card ↥L) : K = L := by
  apply SetLike.coe_injective
  refine Set.eq_of_subset_of_ncard_le hle ?_ (Set.toFinite _)
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, SetLike.coe_sort_coe]
  exact hc.ge
/--
[Submodule_not_exists_cofixed_line_of_inertia_and_branch_swap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_not_exists_cofixed_line_of_inertia_and_branch_swap.lean)
-/
@[path]
private lemma main
    {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    {V : Type*} [AddCommGroup V] [Module (ZMod p) V] (hcard : Nat.card V = p ^ 2)
    {G : Type*} [SMul G V] {I : Set G} {M : Submodule (ZMod p) V}
    (hMtop : M ≠ ⊤)
    (hIquo : ∀ τ ∈ I, ∀ y : V, τ • y - y ∈ M)
    (hIram : ∃ τ ∈ I, ∃ y : V, τ • y ≠ y)
    (hswap : ∃ σ : G, ∀ y : V, y ∉ M → σ • y + y ∈ M) :
    ¬ ∃ N : Submodule (ZMod p) V,
        (∀ g : G, ∀ x ∈ N, g • x ∈ N) ∧ N ≠ ⊥ ∧ N ≠ ⊤ ∧
          ∀ g : G, ∀ y : V, g • y - y ∈ N := by
  have hfin : Finite V :=
    Nat.finite_of_card_ne_zero (hcard ▸ pow_ne_zero 2 hp.pos.ne')
  have hcardp : ∀ L : Submodule (ZMod p) V, L ≠ ⊥ → L ≠ ⊤ → Nat.card ↥L = p := by
    intro L hLbot hLtop
    have hdvd : Nat.card ↥L ∣ p ^ 2 := by
      rw [← hcard, L.card_eq_card_quotient_mul_card]; exact dvd_mul_right _ _
    obtain ⟨k, hk, hkN⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    interval_cases k
    · exact absurd
        (have := (Nat.card_eq_one_iff_unique.mp (by simpa using hkN)).1
         Submodule.eq_bot_of_subsingleton) hLbot
    · simpa using hkN
    · exact absurd (Submodule.eq_top_of_card_eq' (hkN.trans hcard.symm)) hLtop
  rintro ⟨N, _hNstab, hNbot, hNtop, hNcof⟩
  rcases eq_or_ne N M with hNM | hNM
  ·
    subst hNM
    obtain ⟨y, hy⟩ : ∃ y : V, y ∉ N := by
      by_contra h
      exact hNtop (eq_top_iff.mpr fun x _ => not_not.mp (fun hx => h ⟨x, hx⟩))
    obtain ⟨σ, hσ⟩ := hswap
    have h3 : (σ • y + y) - (σ • y - y) ∈ N := N.sub_mem (hσ y hy) (hNcof σ y)
    have h4 : (2 : ZMod p) • y ∈ N := by
      rwa [show (σ • y + y) - (σ • y - y) = (2 : ZMod p) • y by
        rw [two_smul]; abel] at h3
    have hp' : Fact p.Prime := ⟨hp⟩
    have h2ne : (2 : ZMod p) ≠ 0 := by
      have h2' : ((2 : ℕ) : ZMod p) ≠ 0 :=
        fun h => hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
          ((ZMod.natCast_eq_zero_iff 2 p).mp h))
      exact_mod_cast h2'
    exact hy ((N.smul_mem_iff h2ne).mp h4)
  ·
    have hinf : M ⊓ N = ⊥ := by
      rcases eq_or_ne M ⊥ with hM | hM
      · simp [hM]
      by_contra hMN'
      have hcI : Nat.card ↥(M ⊓ N) = p := hcardp (M ⊓ N) hMN'
        (fun h => hNtop (top_le_iff.mp (h ▸ inf_le_right)))
      exact hNM ((Submodule.eq_of_le_of_card_eq' inf_le_right
          (hcI.trans (hcardp N hNbot hNtop).symm)).symm.trans
        (Submodule.eq_of_le_of_card_eq' inf_le_left
          (hcI.trans (hcardp M hM hMtop).symm)))
    obtain ⟨τ, hτI, y, hτy⟩ := hIram
    have : τ • y - y ∈ M ⊓ N := ⟨hIquo τ hτI y, hNcof τ y⟩
    rw [hinf, Submodule.mem_bot] at this
    exact hτy (sub_eq_zero.mp this)

-- created on 2026-10-20
