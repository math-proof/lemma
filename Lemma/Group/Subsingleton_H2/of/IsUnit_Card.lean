import Mathlib
import sympy.Basic

open CategoryTheory Finset

/--
[groupCohomology_subsingleton_H2_of_isUnit_card](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_subsingleton_H2_of_isUnit_card.lean)
-/

private lemma sum_reindex_mulLeft {k G : Type u} [CommRing k] [Group G] [Fintype G]
    {A : Rep k G} (F : G → A) (g : G) :
    ∑ h : G, F (g * h) = ∑ h : G, F h :=
  Fintype.sum_equiv (Equiv.mulLeft g) _ _ fun _ => rfl
@[main]
private lemma main
  {k G : Type u} [CommRing k] [Group G] [Fintype G]
  {A : Rep k G}
-- given
  (hG : IsUnit ((Fintype.card G : k))) :
-- imply
  Subsingleton (groupCohomology.H2 A) := by
-- proof
  have hle : groupCohomology.cocycles₂ A ≤ groupCohomology.coboundaries₂ A := by
    intro f hf
    set σ : G → A := fun x => ∑ j : G, f (x, j) with hσ
    have key : ∀ g h : G, (Fintype.card G) • f (g, h) = A.ρ g (σ h) - σ (g * h) + σ g := by
      intro g h
      have h1 : (∑ j : G, (f (g * h, j) + f (g, h)))
          = ∑ j : G, (A.ρ g (f (h, j)) + f (g, h * j)) :=
        Finset.sum_congr rfl fun j _ => (groupCohomology.mem_cocycles₂_iff f).1 hf g h j
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← map_sum, Finset.sum_const,
        Finset.card_univ, sum_reindex_mulLeft (fun j => f (g, j)) h] at h1
      rw [eq_comm, ← sub_eq_iff_eq_add'] at h1
      rw [← h1]; abel
    refine ⟨fun x => (↑hG.unit⁻¹ : k) • σ x, funext fun gh => ?_⟩
    obtain ⟨g, h⟩ := gh
    have heq : A.ρ g ((↑hG.unit⁻¹ : k) • σ h) - (↑hG.unit⁻¹ : k) • σ (g * h)
        + (↑hG.unit⁻¹ : k) • σ g = (↑hG.unit⁻¹ : k) • (A.ρ g (σ h) - σ (g * h) + σ g) := by
      simp only [map_smul, smul_sub, smul_add]
    rw [groupCohomology.d₁₂_hom_apply, heq, ← key g h, ← Nat.cast_smul_eq_nsmul k,
      smul_smul, hG.val_inv_mul, one_smul]
  exact subsingleton_of_forall_eq 0 fun x =>
    groupCohomology.H2_induction_on x fun y =>
      (groupCohomology.H2π_eq_zero_iff y).2 (hle y.2)


-- created on 2026-10-05
