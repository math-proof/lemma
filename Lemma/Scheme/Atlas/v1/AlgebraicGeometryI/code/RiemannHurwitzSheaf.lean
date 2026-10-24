import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzSheaf
open Ideal


/--
[local_ramification_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma local_ramification_nonneg
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDomain S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  (0 : ℤ) ≤ ∑ P ∈ primesOverFinset p S, ((p.ramificationIdx P : ℤ) - 1) := by
-- proof
  apply Finset.sum_nonneg
  intro P hP
  have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
  have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
  have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
  omega
set_option linter.unusedSectionVars false in

/--
[local_ramification_le_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma local_ramification_le_finrank
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDomain S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra R K]
  [IsFractionRing R K]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  ∑ P ∈ primesOverFinset p S, ((p.ramificationIdx P : ℤ) - 1) ≤ Module.finrank K L := by
-- proof
  have hfund := sum_ramification_inertia S K L hp0
  calc ∑ P ∈ primesOverFinset p S,
    ((p.ramificationIdx P : ℤ) - 1)
    ≤ ∑ P ∈ primesOverFinset p S,
      (p.ramificationIdx P : ℤ) := by
        apply Finset.sum_le_sum; intro P _; omega
    _ ≤ ∑ P ∈ primesOverFinset p S,
      ((p.ramificationIdx P * inertiaDeg p P : ℕ) : ℤ) := by
      apply Finset.sum_le_sum
      intro P hP
      have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
      have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
      exact_mod_cast Nat.le_mul_of_pos_right _ (inertiaDeg_pos p P)
    _ = (Module.finrank K L : ℤ) := by exact_mod_cast hfund
set_option linter.unusedSectionVars false in

/--
[local_ramification_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma local_ramification_eq_zero_iff
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDomain S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  (∑ P ∈ primesOverFinset p S, ((p.ramificationIdx P : ℤ) - 1)) = 0 ↔ ∀ P ∈ primesOverFinset p S, p.ramificationIdx P = 1 := by
-- proof
  rw [Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h P hP
      have := h P hP
      have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
      have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
      have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
      omega
    · intro h P hP
      simp [h P hP]
  · intro P hP
    have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
    have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
    have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
    omega

/--
[DVR_ef_product_eq_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma DVR_ef_product_eq_degree
  [CommRing R]
  [IsDomain R]
  [IsDedekindDomain R]
  [CommRing S]
  [IsDomain S]
  [IsDedekindDomain S]
  [Algebra R S]
  [NoZeroSMulDivisors R S]
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  [CommRing S]
  [IsDomain S]
  [IsDiscreteValuationRing S]
  [Algebra R S]
  {K L : Type*}
  [Field K]
  [Field L]
  [Algebra R K]
  [IsFractionRing R K]
  [Algebra S L]
  [IsFractionRing S L]
  [Algebra K L]
  [Algebra R L]
  [IsScalarTower R S L]
  [IsScalarTower R K L]
  [Module.Finite R S]
  [IsDedekindDomain R]
  [IsDedekindDomain S]
-- given
  (hp0 : IsLocalRing.maximalIdeal R ≠ ⊥) :
-- imply
  (IsLocalRing.maximalIdeal R).ramificationIdx (IsLocalRing.maximalIdeal S) * inertiaDeg (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) = Module.finrank K L :=
-- proof
  ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0
section GenusConsequences

/--
[genus_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma genus_lower_bound
  {gX gY n degR : ℤ}
-- given
  (hRH : 2 * gX - 2 = n * (2 * gY - 2) + degR)
  (hdegR : 0 ≤ degR) :
-- imply
  gX ≥ n * (gY - 1) + 1 := by
-- proof
  linarith

/--
[genus_growth_ramified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma genus_growth_ramified
  {gX gY n degR : ℤ}
-- given
  (hRH : 2 * gX - 2 = n * (2 * gY - 2) + degR)
  (hdegR : 0 ≤ degR)
  (hn : n ≥ 2)
  (hgY : gY ≥ 2) :
-- imply
  gX > gY := by
-- proof
  have := genus_lower_bound gX gY n degR hRH hdegR
  nlinarith

/--
[riemann_hurwitz_P1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma riemann_hurwitz_P1
  {gX n degR : ℤ}
-- given
  (hRH : 2 * gX - 2 = n * (2 * 0 - 2) + degR) :
-- imply
  2 * gX - 2 = -2 * n + degR := by
-- proof
  linarith

/--
[hyperelliptic_branch_points_from_sheaf](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma hyperelliptic_branch_points_from_sheaf
  {gX degR : ℤ}
-- given
  (hRH : 2 * gX - 2 = 2 * (2 * 0 - 2) + degR) :
-- imply
  degR = 2 * gX + 2 := by
-- proof
  linarith

/--
[etale_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma etale_genus
  {gX gY n : ℤ}
-- given
  (hRH : 2 * gX - 2 = n * (2 * gY - 2) + 0) :
-- imply
  gX = n * gY - n + 1 := by
-- proof
  linarith

/--
[etale_double_cover_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma etale_double_cover_genus
  {gX gY : ℤ}
-- given
  (hRH : 2 * gX - 2 = 2 * (2 * gY - 2) + 0) :
-- imply
  gX = 2 * gY - 1 := by
-- proof
  linarith
end GenusConsequences
section Examples

/--
[elliptic_curve_RH_verification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma elliptic_curve_RH_verification
-- imply
  (2 : ℤ) * 1 - 2 = 2 * (2 * 0 - 2) + 4 := by
-- proof
norm_num

/--
[genus2_hyperelliptic_verification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma genus2_hyperelliptic_verification
-- imply
  (2 : ℤ) * 2 - 2 = 2 * (2 * 0 - 2) + 6 := by
-- proof
norm_num

/--
[etale_double_cover_genus2_verification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma etale_double_cover_genus2_verification
-- imply
  (2 : ℤ) * 3 - 2 = 2 * (2 * 2 - 2) + 0 := by
-- proof
norm_num

/--
[degree3_genus1_verification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzSheaf.lean)
-/
@[path]
lemma degree3_genus1_verification
-- imply
  (2 : ℤ) * 1 - 2 = 3 * (2 * 0 - 2) + 6 := by
-- proof
norm_num
end Examples


-- created on 2026-10-23
