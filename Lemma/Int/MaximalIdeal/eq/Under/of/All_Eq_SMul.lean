import Mathlib
import sympy.Basic

open Pointwise

/--
[Algebra_IsInvariant_exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsInvariant_exists_isLocalRing_maximalIdeal_eq_under_of_forall_isMaximal_exists_smul_eq.lean)
-/
@[main]
private lemma main
  [Group G] [Finite G]
  {A B : Type*} [CommRing A] [CommRing B] [Algebra A B] [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G] [Algebra.IsIntegral A B] [FaithfulSMul A B]
  {𝔓 : Ideal B} [𝔓.IsMaximal]
-- given
  (htrans : ∀ Q : Ideal B, Q.IsMaximal → ∃ g : G, Q = g • 𝔓) :
-- imply
  ∃ _ : IsLocalRing A, IsLocalRing.maximalIdeal A = Ideal.under A 𝔓 := by
-- proof
  classical
  have h𝔓 : 𝔓.IsMaximal := ‹_›
  haveI : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact h𝔓.ne_top (Subsingleton.elim _ _)
  haveI : Nontrivial A := (algebraMap A B).domain_nontrivial

  have hp : (Ideal.under A 𝔓).IsMaximal := Ideal.IsMaximal.under A 𝔓

  have hunder : ∀ g : G, Ideal.under A (g • 𝔓) = Ideal.under A 𝔓 := by
    intro g
    ext a
    rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap,
      Ideal.mem_pointwise_smul_iff_inv_smul_mem, smul_algebraMap]

  have huniq : ∀ 𝔪 : Ideal A, 𝔪.IsMaximal → 𝔪 = Ideal.under A 𝔓 := by
    intro 𝔪 h𝔪
    have hker : RingHom.ker (algebraMap A B) ≤ 𝔪 := by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (FaithfulSMul.algebraMap_injective A B)]
      exact bot_le
    obtain ⟨Q, hQmax, hQ⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral 𝔪 hker
    obtain ⟨g, rfl⟩ := htrans Q hQmax
    rw [← hQ]
    exact hunder g
  haveI hloc : IsLocalRing A := IsLocalRing.of_unique_max_ideal ⟨Ideal.under A 𝔓, hp, huniq⟩
  exact ⟨hloc, (IsLocalRing.eq_maximalIdeal hp).symm⟩


-- created on 2026-10-05
