import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[HopfAlgebra_exists_unit_pow_of_torsor_grading_nsmul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_HopfAlgebra_exists_unit_pow_of_torsor_grading_nsmul.lean)
-/
@[path]
private lemma main
  {Λ : Type} [AddCommGroup Λ]
  {R T : Type} [CommRing R] [CommRing T] [Algebra R T]
  (hinj : Function.Injective (algebraMap R T))
  (L : Λ → Submodule R T)
  (hL0 : L 0 = Submodule.span R {(1 : T)})
  (hcyc : ∀ j, ∃ t : T, L j = Submodule.span R {t})
  (hmul : ∀ i j, ∀ x ∈ L i, ∀ y ∈ L j, x * y ∈ L (i + j))
  (htorsor : ∀ i j, L (i + j) ≤ Submodule.span R {z | ∃ x ∈ L i, ∃ y ∈ L j, z = x * y})
  (g : Λ) (Q : ℕ) (hgQ : Q • g = 0) :
  -- imply
  ∃ (t : T) (u : R), IsUnit u ∧ L g = Submodule.span R {t} ∧ t ^ Q = algebraMap R T u ∧ ∀ j : ℕ, L (j • g) = Submodule.span R {t ^ j} := by
  -- proof
  obtain ⟨t, ht⟩ := hcyc g
  have key : ∀ j : ℕ, L (j • g) = Submodule.span R {t ^ j} := by
    intro j
    induction j with
    | zero =>
      rw [zero_nsmul, pow_zero]
      apply hL0
    | succ j ih =>
      rw [succ_nsmul, pow_succ]
      apply le_antisymm
      ·
        refine (htorsor _ _).trans (Submodule.span_le.mpr ?_)
        rintro z ⟨x, hx, y, hy, rfl⟩
        rw [ih, Submodule.mem_span_singleton] at hx
        rw [ht, Submodule.mem_span_singleton] at hy
        obtain ⟨a, rfl⟩ := hx
        obtain ⟨b, rfl⟩ := hy
        rw [SetLike.mem_coe, Submodule.mem_span_singleton]
        refine ⟨a * b, ?_⟩
        rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul]
        ring
      ·
        rw [Submodule.span_le, Set.singleton_subset_iff]
        have h1 : t ^ j ∈ L (j • g) := by
          rw [ih]
          apply Submodule.mem_span_singleton_self _
        have h2 : t ∈ L g := by
          rw [ht]
          apply Submodule.mem_span_singleton_self _
        refine hmul _ _ _ h1 _ h2
  have hLq : Submodule.span R {(1 : T)} = Submodule.span R {t ^ Q} := by
    rw [← hL0, ← hgQ, key Q]
  have htq : t ^ Q ∈ Submodule.span R {(1 : T)} := by
    rw [hLq]
    apply Submodule.mem_span_singleton_self _
  have h1m : (1 : T) ∈ Submodule.span R {t ^ Q} := by
    rw [← hLq]
    apply Submodule.mem_span_singleton_self _
  rw [Submodule.mem_span_singleton] at htq h1m
  obtain ⟨u, hu⟩ := htq
  obtain ⟨c, hc⟩ := h1m
  refine ⟨t, u, ?_, ht, ?_, key⟩
  ·
    have hcu : algebraMap R T (c * u) = algebraMap R T 1 := by
      rw [map_one, map_mul]
      calc
        _ = c • (u • (1 : T)) := by
          rw [Algebra.smul_def, Algebra.smul_def]
          ring
        _ = c • (t ^ Q) := by
          rw [hu]
        _ = 1 := hc
    have hcu1 : c * u = 1 := hinj hcu
    refine ⟨⟨u, c, ?_, hcu1⟩, rfl⟩
    rw [mul_comm]
    apply hcu1
  ·
    rw [← hu, Algebra.smul_def, mul_one]


-- created on 2026-10-20
