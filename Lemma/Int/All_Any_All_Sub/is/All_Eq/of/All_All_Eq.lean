import Mathlib
import sympy.Basic

open CategoryTheory groupCohomology

/--
[groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {A : Rep.{u} k G}
  {S : Subgroup G}
  {c : cocycles₁ (Rep.res S.subtype A)}
-- given
  (htriv : ∀ s ∈ S, ∀ v : A, A.ρ s v = v) :
-- imply
  (∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
        A.ρ g (c t) - c s = A.ρ (s : G) a - a) ↔
      ∀ (g : G) (s t : S), (g⁻¹ * s * g : G) = t → A.ρ g (c t) = c s := by
-- proof
  constructor
  · intro h g s t hst
    obtain ⟨a, ha⟩ := h g
    have := ha s t hst
    rwa [htriv _ s.2, sub_self, sub_eq_zero] at this
  · intro h g
    exact ⟨0, fun s t hst => by rw [h g s t hst, sub_self, map_zero, sub_self]⟩


-- created on 2026-10-05
