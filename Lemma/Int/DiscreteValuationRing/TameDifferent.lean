import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.RingTheory.DiscreteValuationRing.TameDifferent
open IsLocalRing
open scoped nonZeroDivisors


/--
[differentIdeal_eq_maximalIdeal_pow_sub_one_of_isUnit_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/TameDifferent.lean)
-/
@[path]
lemma differentIdeal_eq_maximalIdeal_pow_sub_one_of_isUnit_natCast
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  {e : ℕ}
-- given
  (heUnit : IsUnit (e : B))
  (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e) :
-- imply
  differentIdeal A B = maximalIdeal B ^ (e - 1) := by
-- proof
  apply le_antisymm
  · apply Ideal.dvd_iff_le.mp
    apply pow_sub_one_dvd_differentIdeal (p := maximalIdeal A)
      A (maximalIdeal B) e
    · exact IsDiscreteValuationRing.not_a_field A
    · rw [← he]
  · obtain ⟨b, hb⟩ :=
    intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow
      A B e heUnit he 1
    have hnot : Algebra.intTrace A B b ∉ maximalIdeal A := by
      simp [hb]
    have hnotdvd : ¬ maximalIdeal B ^ e ∣ differentIdeal A B := by
      apply not_dvd_differentIdeal_of_intTrace_not_mem A
        (maximalIdeal B ^ e) ⊤ (x := b)
      · simpa only [Ideal.mul_top] using he.symm
      · exact Submodule.mem_top
      · exact hnot
    have hDne : differentIdeal A B ≠ ⊥ := differentIdeal_ne_bot
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
    obtain ⟨d, hd⟩ :=
      IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hDne hϖ
    have hDpow : differentIdeal A B = maximalIdeal B ^ d := by
      rwa [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    have hde : d < e := by
      apply Nat.lt_of_not_ge
      intro hed
      apply hnotdvd
      rw [hDpow]
      exact pow_dvd_pow _ hed
    rw [hDpow]
    exact Ideal.pow_le_pow_right (Nat.le_sub_one_of_lt hde)


-- created on 2026-10-20
-- updated on 2026-10-26
