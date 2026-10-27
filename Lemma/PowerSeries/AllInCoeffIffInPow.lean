import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[RingHom_forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_forall_coeff_mem_iff_mem_pow_sup_map_of_forall_coeff_eq_zero_iff.lean)
-/
@[path]
private lemma main
  [CommRing R] [CommRing A] [Algebra R A] (θ : A →+* PowerSeries R) (I : Ideal A)
    (hC : ∀ r : R, θ (algebraMap R A r) = PowerSeries.C r)
    (hfil : ∀ (n : ℕ) (a : A), (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = 0) ↔ a ∈ I ^ n)
    (hsurj : ∀ (n : ℕ) (p : PowerSeries R), ∃ a : A, ∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) = PowerSeries.coeff k p)
    (𝔪 : Ideal R) (n : ℕ) (a : A) :
    -- imply
    (∀ k : ℕ, k < n → PowerSeries.coeff k (θ a) ∈ 𝔪) ↔ a ∈ I ^ n ⊔ 𝔪.map (algebraMap R A) := by
    -- proof
  classical
  constructor
  ·
    intro h
    choose b hb using fun k : ℕ => hsurj n (PowerSeries.X ^ k)
    set a'' : A := ∑ k ∈ Finset.range n, algebraMap R A (PowerSeries.coeff k (θ a)) * b k with ha''
    have hmem : a'' ∈ 𝔪.map (algebraMap R A) := by
      refine Ideal.sum_mem _ fun k hk => ?_
      apply Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (h k (Finset.mem_range.mp hk)))
    have hlow : ∀ k : ℕ, k < n → PowerSeries.coeff k (θ (a - a'')) = 0 := by
      intro k hk
      rw [map_sub, map_sub, ha'', map_sum, map_sum]
      simp only [map_mul, hC, PowerSeries.coeff_C_mul]
      have : ∀ j ∈ Finset.range n, PowerSeries.coeff k (θ a) * 0 = 0 := fun _ _ => mul_zero _
      rw [Finset.sum_eq_single k]
      ·
        rw [hb k k hk, PowerSeries.coeff_X_pow, ite_eq_left rfl, mul_one, sub_self]
      ·
        intro j hj hjk
        rw [hb j k hk, PowerSeries.coeff_X_pow, ite_eq_right (Ne.symm hjk), mul_zero]
      ·
        intro hk'
        apply absurd (Finset.mem_range.mpr hk) hk'
    have hIn : a - a'' ∈ I ^ n := (hfil n _).mp hlow
    have : a = (a - a'') + a'' := by ring
    rw [this]
    apply Submodule.add_mem_sup hIn hmem
  ·
    intro h k hk
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp h
    rw [map_add, map_add]
    refine 𝔪.add_mem ?_ ?_
    ·
      rw [((hfil n y).mpr hy) k hk]
      apply 𝔪.zero_mem
    ·
      suffices hall : ∀ z ∈ 𝔪.map (algebraMap R A), ∀ j : ℕ, PowerSeries.coeff j (θ z) ∈ 𝔪 from hall z hz k
      intro z hz
      refine Submodule.span_induction (p := fun z _ => ∀ j : ℕ, PowerSeries.coeff j (θ z) ∈ 𝔪) ?_ ?_ ?_ ?_ hz
      ·
        rintro _ ⟨m, hm, rfl⟩ j
        rw [hC, PowerSeries.coeff_C]
        split_ifs
        · apply hm
        · apply 𝔪.zero_mem
      ·
        intro j
        rw [map_zero, map_zero]
        apply 𝔪.zero_mem
      ·
        intro x y _ _ hx hy j
        rw [map_add, map_add]
        apply 𝔪.add_mem (hx j) (hy j)
      ·
        intro c x _ hx j
        rw [smul_eq_mul, map_mul, PowerSeries.coeff_mul]
        apply Ideal.sum_mem _ fun ij _ => Ideal.mul_mem_left _ _ (hx ij.2)


-- created on 2026-10-20
