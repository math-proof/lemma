import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealPowQuotientTrace
open IsLocalRing


/--
[trace_residueFieldMaximalIdealPowQuotient_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean)
-/
@[path]
private lemma trace_residueFieldMaximalIdealPowQuotient_succ_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
  {n : ℕ} [Module (ResidueField A) (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)] [IsScalarTower (ResidueField A) (ResidueField B) (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)] [FiniteDimensional (ResidueField A) (ResidueFieldMaximalIdealPowQuotient A B (n + 1))]
  {b : B}
-- given
  (hSucc : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ (n + 1)) :
-- imply
  Algebra.trace (ResidueField A)
    (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
    (Ideal.Quotient.mk _ b) =
    Algebra.trace (ResidueField A) (ResidueField B)
    (IsLocalRing.residue B b) +
    Algebra.trace (ResidueField A)
    (ResidueFieldMaximalIdealPowQuotient A B n)
    (Ideal.Quotient.mk _ b) := by
-- proof
  apply trace_residueFieldMaximalIdealPowQuotient_succ A B n hSucc b

/--
[trace_residueFieldMaximalIdealPowQuotient](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean)
-/
@[path]
private lemma trace_residueFieldMaximalIdealPowQuotient_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
  {n : ℕ} [FiniteDimensional (ResidueField A) (ResidueFieldMaximalIdealPowQuotient A B n)]
  {b : B}
-- given
  (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n) :
-- imply
  Algebra.trace (ResidueField A)
    (ResidueFieldMaximalIdealPowQuotient A B n)
    (Ideal.Quotient.mk _ b) =
    n • Algebra.trace (ResidueField A) (ResidueField B)
    (IsLocalRing.residue B b) := by
-- proof
  apply trace_residueFieldMaximalIdealPowQuotient A B n h b

/--
[residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean)
-/
@[path]
private lemma residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B]
  {e : ℕ}
  {b : B}
-- given
  (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e) :
-- imply
  residue A (Algebra.intTrace A B b) =
    e • Algebra.trace (ResidueField A)
    (ResidueField B) (residue B b) := by
-- proof
  apply residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow A B e he b

/--
[intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean)
-/
@[path]
private lemma intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow_eq
  [CommRing A] [CommRing B] [IsDomain A] [IsDomain B] [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B] [Module.IsTorsionFree A B] [Module.Finite A B] [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
  {e : ℕ}
-- given
  (heUnit : IsUnit (e : B))
  (he : Ideal.map (algebraMap A B) (maximalIdeal A) = maximalIdeal B ^ e) :
-- imply
  Function.Surjective (Algebra.intTrace A B) := by
-- proof
  apply intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow A B e heUnit he


-- created on 2026-10-20
