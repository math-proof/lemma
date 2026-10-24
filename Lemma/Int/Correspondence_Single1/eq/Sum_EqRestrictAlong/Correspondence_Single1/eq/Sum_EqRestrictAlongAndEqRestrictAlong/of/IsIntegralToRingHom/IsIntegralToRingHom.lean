import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Lemma.Int.P2MUtil

open AlgebraicCurve Classical

/--
[AlgebraicCurve_Divisor_correspondence_single_one_apply_eq_sum_and_eq_finsum](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_Divisor_correspondence_single_one_apply_eq_sum_and_eq_finsum.lean)
-/

private lemma  correspondence_single_one_apply
  {K F F' : Type*}
  [Field K]
  [Field F]
  [Field F']
  [Algebra K F]
  [Algebra K F']
  [HasPrincipalDivisors K F']
  (φ ψ : F →ₐ[K] F')
  (hφ : φ.toRingHom.IsIntegral)
  (hψ : ψ.toRingHom.IsIntegral)
  (x y : Place K F) :
  Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
    ∑ W ∈ Place.fiberAlong φ hφ x,
      if W.restrictAlong ψ hψ = y then
        (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Divisor.pushforwardAlong_single, Finsupp.single_apply, one_mul]
  all_goals (split_ifs <;> rfl)

open in

private lemma  correspondence_single_one_apply_eq_finsum
  {K F F' : Type*}
  [Field K]
  [Field F]
  [Field F']
  [Algebra K F]
  [Algebra K F']
  [HasPrincipalDivisors K F']
  (φ ψ : F →ₐ[K] F')
  (hφ : φ.toRingHom.IsIntegral)
  (hψ : ψ.toRingHom.IsIntegral)
  (x y : Place K F) :
  Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
    ∑ᶠ W : Place K F',
      if W.restrictAlong φ hφ = x ∧ W.restrictAlong ψ hψ = y then
        (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [correspondence_single_one_apply]
  symm
  rw [finsum_eq_sum_of_support_subset _ (s := Place.fiberAlong φ hφ x)]
  ·
    refine Finset.sum_congr rfl fun W hW => ?_
    rw [Place.mem_fiberAlong] at hW
    simp only [hW, true_and]
  ·
    intro W hW
    rw [Function.mem_support] at hW
    simp only [Finset.mem_coe, Place.mem_fiberAlong]
    by_contra hx
    exact hW (ite_eq_right fun h => hx h.1)
@[path]
private lemma main
  {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [HasPrincipalDivisors K F']
  {φ ψ : F →ₐ[K] F'}
  {x y : Place K F}
-- given
  (hφ : φ.toRingHom.IsIntegral)
  (hψ : ψ.toRingHom.IsIntegral) :
-- imply
  (Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ W ∈ Place.fiberAlong φ hφ x,
        if W.restrictAlong ψ hψ = y then (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0) ∧
    (Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ᶠ W : Place K F',
        if W.restrictAlong φ hφ = x ∧ W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0) := by
-- proof
  exact ⟨correspondence_single_one_apply φ ψ hφ hψ x y,
    correspondence_single_one_apply_eq_finsum φ ψ hφ hψ x y⟩


-- created on 2026-10-23
