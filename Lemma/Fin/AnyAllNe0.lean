import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma card_zeroSet_le
  [Field 𝔽] [Fintype 𝔽]
  [AddCommGroup V] [Module 𝔽 V]
  {n : ℕ} {φ : AffineMap 𝔽 (Fin n → 𝔽) V} [DecidablePred fun x : Fin n → 𝔽 => φ x = 0]
  -- given
  (hn : 0 < n)
  (hφ : ∃ x, φ x ≠ 0) :
  -- imply
  (Finset.univ.filter fun x : Fin n → 𝔽 => φ x = 0).card ≤ Fintype.card 𝔽 ^ (n - 1) := by
  -- proof
  classical
  if hZ : (Finset.univ.filter fun x : Fin n → 𝔽 => φ x = 0) = ∅ then
    rw [hZ, Finset.card_empty]
    apply Nat.zero_le
  else
    obtain ⟨x₀, hx₀⟩ := Iff.mpr Finset.nonempty_iff_ne_empty hZ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx₀
    let K : Submodule 𝔽 (Fin n → 𝔽) := LinearMap.ker φ.linear
    have hmem : ∀ x, φ x = 0 ↔ x - x₀ ∈ K := fun x => by
      change φ x = 0 ↔ φ.linear (x - x₀) = 0
      have h := φ.linearMap_vsub x x₀
      simp only [vsub_eq_sub] at h
      rw [h, hx₀, sub_zero]
    have hK : K ≠ ⊤ := by
      intro htop
      obtain ⟨x, hx⟩ := hφ
      apply hx (Iff.mpr (hmem x) (htop ▸ Submodule.mem_top))
    have hlt : Module.finrank 𝔽 K < n := by
      simpa using Submodule.finrank_lt hK
    have hcard : (Finset.univ.filter fun x : Fin n → 𝔽 => φ x = 0).card ≤ Fintype.card K := by
      rw [← Fintype.card_coe]
      refine Fintype.card_le_of_injective (fun x => ⟨x.1 - x₀, Iff.mp (hmem x.1) (Iff.mp Finset.mem_filter x.2).2⟩) ?_
      intro a b h
      have : a.1 - x₀ = b.1 - x₀ := congrArg Subtype.val h
      apply Subtype.ext (sub_left_injective this)
    calc
      _ ≤ Fintype.card K := hcard
      _ = Fintype.card 𝔽 ^ Module.finrank 𝔽 K := Module.card_eq_pow_finrank (K := 𝔽) (V := K)
      _ ≤ Fintype.card 𝔽 ^ (n - 1) := Nat.pow_le_pow_right Fintype.card_pos (by omega)

/--
[FiniteField_exists_forall_affineMap_ne_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_FiniteField_exists_forall_affineMap_ne_zero.lean)
-/
@[path]
private lemma main
  [Field 𝔽] [Fintype 𝔽]
  {ι : Type} [Fintype ι]
  {V : ι → Type} [∀ j, AddCommGroup (V j)] [∀ j, Module 𝔽 (V j)]
  {n : ℕ}
  {φ : ∀ j, AffineMap 𝔽 (Fin n → 𝔽) (V j)}
  -- given
  (hφ : ∀ j, ∃ x, φ j x ≠ 0)
  (hm : Fintype.card ι < Fintype.card 𝔽) :
  -- imply
  ∃ x, ∀ j, φ j x ≠ 0 := by
  -- proof
  classical
  obtain rfl | hn := Nat.eq_zero_or_pos n
  ·
    refine ⟨fun i => i.elim0, fun j => ?_⟩
    obtain ⟨x, hx⟩ := hφ j
    rwa [Subsingleton.elim x (fun i => i.elim0)] at hx
  by_contra hcon
  push Not at hcon
  have hcover : (Finset.univ : Finset (Fin n → 𝔽)) ⊆ Finset.univ.biUnion fun j => Finset.univ.filter fun x : Fin n → 𝔽 => φ j x = 0 := by
    intro x _
    obtain ⟨j, hj⟩ := hcon x
    apply Iff.mpr Finset.mem_biUnion ⟨j, Finset.mem_univ j, by simpa using hj⟩
  have h1 : Fintype.card 𝔽 ^ n ≤ Fintype.card ι * Fintype.card 𝔽 ^ (n - 1) := calc
    _ = (Finset.univ : Finset (Fin n → 𝔽)).card := by simp
    _ ≤ (Finset.univ.biUnion fun j => Finset.univ.filter fun x : Fin n → 𝔽 => φ j x = 0).card := Finset.card_le_card hcover
    _ ≤ ∑ j, (Finset.univ.filter fun x : Fin n → 𝔽 => φ j x = 0).card := Finset.card_biUnion_le
    _ ≤ ∑ _ : ι, Fintype.card 𝔽 ^ (n - 1) := Finset.sum_le_sum fun j _ => card_zeroSet_le hn (hφ j)
    _ = Fintype.card ι * Fintype.card 𝔽 ^ (n - 1) := by simp
  have h2 : Fintype.card ι * Fintype.card 𝔽 ^ (n - 1) < Fintype.card 𝔽 * Fintype.card 𝔽 ^ (n - 1) := Nat.mul_lt_mul_of_pos_right hm (pow_pos Fintype.card_pos _)
  have h3 : Fintype.card 𝔽 * Fintype.card 𝔽 ^ (n - 1) = Fintype.card 𝔽 ^ n := by
    rw [← pow_succ']
    congr 1
    omega
  omega


-- created on 2026-10-20
