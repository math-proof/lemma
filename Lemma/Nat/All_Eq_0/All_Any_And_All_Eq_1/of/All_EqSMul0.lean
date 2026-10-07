import Mathlib
import sympy.Basic


/--
[MonoidHom_forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MonoidHom_forall_eq_one_imp_eq_zero_and_exists_ne_zero_forall_mem_apply_eq_one.lean)
-/
@[main]
private lemma main
  [AddCommGroup M] [Finite M] [Field L] [IsAlgClosed L] [CharZero L]
  {p : ℕ} [Fact p.Prime]
-- given
  (_hM : ∀ m : M, p • m = 0) :
-- imply
  (∀ m : M, (∀ χ : Multiplicative M →* Lˣ, χ (Multiplicative.ofAdd m) = 1) → m = 0) ∧
    (∀ K : Subgroup (Multiplicative M →* Lˣ), K ≠ ⊤ →
      ∃ m : M, m ≠ 0 ∧ ∀ χ ∈ K, χ (Multiplicative.ofAdd m) = 1) := by
-- proof
  classical
  have : NeZero ((Monoid.exponent (Multiplicative M) : ℕ) : L) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  have hE : HasEnoughRootsOfUnity L (Monoid.exponent (Multiplicative M)) := inferInstance
  refine ⟨fun m hm => ?_, fun K hK => ?_⟩
  · have h : Multiplicative.ofAdd m = (1 : Multiplicative M) :=
      (CommGroup.forall_apply_eq_apply_iff (Multiplicative M) (M := L)).mp (fun φ => by
        rw [hm φ, map_one])
    exact ofAdd_eq_one.mp h
  · let e := CommGroup.subgroupOrderIsoSubgroupMonoidHom (Multiplicative M) L
    have hH : e.symm (OrderDual.toDual K) ≠ ⊥ := by
      intro h
      apply hK
      have h' : e.symm (OrderDual.toDual K) = e.symm ⊥ := by rw [h, map_bot]
      have h'' := e.symm.injective h'
      exact congrArg OrderDual.ofDual h''
    obtain ⟨⟨g, hg⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
    refine ⟨Multiplicative.toAdd g, ?_, fun χ hχ => ?_⟩
    · intro h0
      apply hg1
      ext
      change g = 1
      rw [← ofAdd_toAdd g, h0, ofAdd_zero]
    · rw [ofAdd_toAdd]
      exact (CommGroup.mem_subgroupOrderIsoSubgroupMonoidHom_symm_iff (M := L) K g).mp hg χ hχ


-- created on 2026-10-05
