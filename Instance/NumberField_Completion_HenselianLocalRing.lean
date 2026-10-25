-- Carved from Lemma/Definitions/Def_NumberField_Completion_HenselianLocalRing.lean: instance decls only.
import Mathlib
import Instance.NumberField_Completion_Finite

set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false

open IsLocalRing Pointwise

noncomputable section

section CompactNoetherianLocal

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CompactSpace R] [T2Space R] [IsNoetherianRing R] [IsLocalRing R]

instance (priority := 80) instIsAdicCompleteMaximalIdealOfCompactSpace :
    IsAdicComplete (maximalIdeal R) R where
  prec' f hf := by

    let S : ℕ → Set R := fun n => f n +ᵥ ((maximalIdeal R ^ n : Ideal R) : Set R)

    have hSclosed : ∀ n, IsClosed (S n) := fun n =>
      (IsNoetherianRing.isClosed_ideal (maximalIdeal R ^ n)).vadd (f n)
    have hSne : ∀ n, (S n).Nonempty := fun n =>
      ⟨f n, ⟨0, Ideal.zero_mem _, by simp⟩⟩

    have hSmono : ∀ n, S (n + 1) ⊆ S n := by
      intro n x ⟨y, hy, hxy⟩
      have hcauchy : f (n + 1) - f n ∈ (maximalIdeal R) ^ n := by
        have h := hf (Nat.le_succ n)
        rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← neg_sub, neg_mem_iff] at h
      exact ⟨(f (n + 1) - f n) + y,
        Ideal.add_mem _ hcauchy (Ideal.pow_le_pow_right (Nat.le_succ n) hy),
        by simp only [vadd_eq_add] at hxy ⊢; linear_combination hxy⟩

    obtain ⟨L, hL⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      hSmono hSne (hSclosed 0).isCompact hSclosed
    refine ⟨L, fun n => ?_⟩
    obtain ⟨y, hy, hLy⟩ := Set.mem_iInter.mp hL n
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    simp only [vadd_eq_add] at hLy
    have h : f n - L = -y := by linear_combination hLy
    rw [h]; exact neg_mem hy


instance (priority := 80) instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing :
    HenselianLocalRing R :=
  henselianLocalRing_of_henselianRing

end CompactNoetherianLocal

section AdicCompletionIntegers

open IsDedekindDomain NumberField

variable (K : Type*) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

instance NumberField.instIsAdicCompleteMaximalIdealAdicCompletionIntegers :
    IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) :=
  instIsAdicCompleteMaximalIdealOfCompactSpace

instance NumberField.instHenselianLocalRingAdicCompletionIntegers :
    HenselianLocalRing (v.adicCompletionIntegers K) :=
  instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing

example : HenselianLocalRing (Valued.integer (v.adicCompletion K)) :=
  inferInstanceAs (HenselianLocalRing (v.adicCompletionIntegers K))

end AdicCompletionIntegers


/-- info: 'instIsAdicCompleteMaximalIdealOfCompactSpace' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instIsAdicCompleteMaximalIdealOfCompactSpace

/-- info: 'instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms instHenselianLocalRingOfCompactSpaceOfIsNoetherianRing

/-- info: 'NumberField.instHenselianLocalRingAdicCompletionIntegers' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms NumberField.instHenselianLocalRingAdicCompletionIntegers

/-- info: 'exists_nthRoot_of_isUnit_natCast' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nthRoot_of_isUnit_natCast

/-- info: 'exists_nthRoot_of_sub_one_mem_maximalIdeal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms exists_nthRoot_of_sub_one_mem_maximalIdeal
