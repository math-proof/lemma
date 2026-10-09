import Mathlib
import sympy.Basic


/--
[ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ArtinL_trace_restrict_invariants_eq_inv_card_mul_sum_trace.lean)
-/
@[path]
private lemma main
  [Field K] [CharZero K] [Group G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {ρ : Representation K G V}
  {I : Subgroup G} [Fintype ↥I]
  {g : G}
-- given
  (h : ∀ v ∈ Representation.invariants (ρ.comp I.subtype), ρ g v ∈ Representation.invariants (ρ.comp I.subtype)) :
-- imply
  LinearMap.trace K _ ((ρ g).restrict h) =
      (Fintype.card ↥I : K)⁻¹ * ∑ τ : ↥I, LinearMap.trace K V (ρ (g * τ)) := by
-- proof
  classical
  have : Invertible (Fintype.card ↥I : K) :=
    invertibleOfNonzero (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

  set W := Representation.invariants (ρ.comp I.subtype) with hW
  have hproj := Representation.isProj_averageMap (ρ.comp I.subtype)
  set e := Representation.averageMap (ρ.comp I.subtype) with he

  have key : LinearMap.trace K W ((ρ g).restrict h) = LinearMap.trace K V (ρ g ∘ₗ e) := by
    let e' : V →ₗ[K] W := e.codRestrict W hproj.map_mem
    have hfac : ρ g ∘ₗ e = W.subtype ∘ₗ (((ρ g).restrict h) ∘ₗ e') := by
      apply LinearMap.ext
      intro v
      rfl
    have hid : e' ∘ₗ W.subtype = LinearMap.id := by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      exact hproj.map_id w w.2
    rw [hfac, LinearMap.trace_comp_comm', LinearMap.comp_assoc, hid, LinearMap.comp_id]
  rw [key, he, Representation.averageMap, GroupAlgebra.average, map_smul, map_sum]
  simp only [Representation.asAlgebraHom_of, LinearMap.comp_smul, map_smul, smul_eq_mul, invOf_eq_inv]
  congr 1
  change (LinearMap.trace K V) (ρ g * ∑ x : ↥I, (ρ.comp I.subtype) x) = _
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  change (LinearMap.trace K V) (ρ g * ρ (τ : G)) = _
  rw [← map_mul]


-- created on 2026-10-05
