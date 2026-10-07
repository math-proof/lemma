import Mathlib
import sympy.Basic

open CategoryTheory

/--
[groupCohomology_H1_subsingleton_of_isUnit_card](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_H1_subsingleton_of_isUnit_card.lean)
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
  Subsingleton (groupCohomology.H1 A) := by
-- proof
  have hle : groupCohomology.cocycles₁ A ≤ groupCohomology.coboundaries₁ A := by
    intro f hf
    set s : A := ∑ h : G, f h with hs
    have key : ∀ g : G, (Fintype.card G) • f g = s - A.ρ g s := by
      intro g
      have h1 : (∑ h : G, f (g * h)) = ∑ h : G, (A.ρ g (f h) + f g) :=
        Finset.sum_congr rfl fun h _ => (groupCohomology.mem_cocycles₁_iff f).1 hf g h
      rw [sum_reindex_mulLeft f g, Finset.sum_add_distrib, ← map_sum, Finset.sum_const,
        Finset.card_univ, ← hs] at h1
      rw [eq_sub_iff_add_eq, add_comm]
      exact h1.symm
    refine ⟨-((↑hG.unit⁻¹ : k) • s), funext fun g => ?_⟩
    show A.ρ g (-((↑hG.unit⁻¹ : k) • s)) - (-((↑hG.unit⁻¹ : k) • s)) = f g
    have heq : A.ρ g (-((↑hG.unit⁻¹ : k) • s)) - -((↑hG.unit⁻¹ : k) • s)
        = (↑hG.unit⁻¹ : k) • (s - A.ρ g s) := by
      simp only [map_neg, map_smul, smul_sub]
      abel
    rw [heq, ← key g, ← Nat.cast_smul_eq_nsmul k, smul_smul, hG.val_inv_mul, one_smul]
  exact subsingleton_of_forall_eq 0 fun x =>
    groupCohomology.H1_induction_on x fun y =>
      (groupCohomology.H1π_eq_zero_iff y).2 (hle y.2)


-- created on 2026-10-05
