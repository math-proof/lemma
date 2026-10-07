import Mathlib
import sympy.Basic


/--
[Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Subgroup_relIndex_inf_map_conj_eq_natCard_setOf_exists_quotientMk_mul_eq.lean)
-/
@[main]
private lemma main
  [Group G]
  {K : Subgroup G}
  {g : G} :
-- imply
  (K ⊓ K.map (MulAut.conj g).toMonoidHom).relIndex K =
      Nat.card {c : G ⧸ K // ∃ k ∈ K, (QuotientGroup.mk (k * g) : G ⧸ K) = c} := by
-- proof
  classical

  have horb : (MulAction.orbit K (QuotientGroup.mk g : G ⧸ K) : Set (G ⧸ K)) =
      {c : G ⧸ K | ∃ k ∈ K, (QuotientGroup.mk (k * g) : G ⧸ K) = c} := by
    ext c
    simp only [MulAction.mem_orbit_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k, k.2, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, hk⟩, rfl⟩
  have hstab : (K ⊓ K.map (MulAut.conj g).toMonoidHom).subgroupOf K =
      MulAction.stabilizer K (QuotientGroup.mk g : G ⧸ K) := by
    ext k
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨-, x, hx, hxk⟩
      show (QuotientGroup.mk ((k : G) * g) : G ⧸ K) = QuotientGroup.mk g
      rw [QuotientGroup.eq]
      have : (k : G) = g * x * g⁻¹ := by rw [← hxk]; rfl
      rw [this]
      simpa [mul_assoc] using K.inv_mem hx
    · intro h
      have h' : (QuotientGroup.mk ((k : G) * g) : G ⧸ K) = QuotientGroup.mk g := h
      rw [QuotientGroup.eq] at h'
      refine ⟨k.2, g⁻¹ * k * g, ?_, ?_⟩
      · have := K.inv_mem h'
        simpa [mul_assoc] using this
      · show g * (g⁻¹ * k * g) * g⁻¹ = k
        group
  rw [Subgroup.relIndex, hstab, MulAction.index_stabilizer, horb, Set.ncard_def]
  rfl


-- created on 2026-10-05
