import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannHurwitzFormula
open Ideal Module RiemannHurwitzFormula


namespace RiemannHurwitzFormula

/--
[DVR_ef_eq_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma DVR_ef_eq_degree
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
  DVRRamificationIndex (R := R) (S := S) * inertiaDeg (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) = finrank K L :=
-- proof
  ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[DVR_unramified_inertiaDeg_eq_degree](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma DVR_unramified_inertiaDeg_eq_degree
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
  (hp0 : IsLocalRing.maximalIdeal R ≠ ⊥)
  (hunr : DVRIsUnramified (R := R) (S := S)) :
-- imply
  inertiaDeg (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S) = finrank K L := by
-- proof
  have h := ramificationIdx_mul_inertiaDeg_of_isLocalRing S K L hp0
  unfold DVRIsUnramified DVRRamificationIndex at hunr
  rwa [hunr, one_mul] at h

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[DVR_ramification_contribution_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma DVR_ramification_contribution_nonneg
  [CommRing R]
  [IsDomain R]
  [IsDiscreteValuationRing R]
  [CommRing S]
  [IsDomain S]
  [IsDiscreteValuationRing S]
  [Algebra R S]
  [IsDedekindDomain R]
  [IsDedekindDomain S]
  [NoZeroSMulDivisors R S]
  [(IsLocalRing.maximalIdeal R).IsMaximal]
  [(IsLocalRing.maximalIdeal S).IsPrime]
  [(IsLocalRing.maximalIdeal S).LiesOver (IsLocalRing.maximalIdeal R)]
-- given
  (hp0 : IsLocalRing.maximalIdeal R ≠ ⊥) :
-- imply
  0 ≤ (DVRRamificationIndex (R := R) (S := S) : ℤ) - 1 := by
-- proof
  unfold DVRRamificationIndex
  have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver
    (IsLocalRing.maximalIdeal S) hp0 (p := IsLocalRing.maximalIdeal R)
  omega
section RamificationDivisorDegree
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  (S : Type*) [CommRing S] [IsDedekindDomain S] [Algebra R S]
  [NoZeroSMulDivisors R S]

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[ramificationDivisorDegreeAt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma ramificationDivisorDegreeAt_nonneg
  [CommRing R]
  [IsDedekindDomain R]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  0 ≤ ramificationDivisorDegreeAt S p hp0 := by
-- proof
  unfold ramificationDivisorDegreeAt
  apply Finset.sum_nonneg
  intro P hP
  have : P.IsPrime := ((mem_primesOverFinset_iff hp0 S).mp hP).1
  have : P.LiesOver p := ((mem_primesOverFinset_iff hp0 S).mp hP).2
  have := IsDedekindDomain.ramificationIdx_ne_zero_of_liesOver P hp0
  omega

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[ramificationDivisorDegreeAt_le_finrank](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma ramificationDivisorDegreeAt_le_finrank
  [CommRing R]
  [IsDedekindDomain R]
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
  ramificationDivisorDegreeAt S p hp0 ≤ finrank K L := by
-- proof
  unfold ramificationDivisorDegreeAt
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
    _ = (finrank K L : ℤ) := by exact_mod_cast hfund

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[ramificationDivisorDegreeAt_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma ramificationDivisorDegreeAt_eq_zero_iff
  [CommRing R]
  [IsDedekindDomain R]
  {p : Ideal R}
  [p.IsMaximal]
-- given
  (hp0 : p ≠ ⊥) :
-- imply
  ramificationDivisorDegreeAt S p hp0 = 0 ↔ ∀ P ∈ primesOverFinset p S, p.ramificationIdx P = 1 := by
-- proof
  unfold ramificationDivisorDegreeAt
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

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_canonical_decomp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_canonical_decomp
  {f : CurveMorphismData}
  {deg_fKY : ℤ}
-- given
  (h_pullback : deg_fKY = f.degree * f.deg_KY)
  (h_canonical : f.deg_KX = deg_fKY + f.deg_R) :
-- imply
  f.deg_KX = f.degree * f.deg_KY + f.deg_R := by
-- proof
  linarith

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_degree_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_degree_corollary
  {f : CurveCovering} :
-- imply
  f.X.degK = f.n * f.Y.degK + f.deg_R :=
-- proof
  f.degK_eq

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_genus_from_data](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_genus_from_data
  {f : CurveMorphismData}
  {g_X g_Y : ℤ}
-- given
  (h_gX : f.deg_KX = 2 * g_X - 2)
  (h_gY : f.deg_KY = 2 * g_Y - 2)
  (h_decomp : f.deg_KX = f.degree * f.deg_KY + f.deg_R) :
-- imply
  2 * g_X - 2 = f.degree * (2 * g_Y - 2) + f.deg_R := by
-- proof
  rw [← h_gX, ← h_gY]; exact h_decomp

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_genus_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_genus_lower_bound
  {f : CurveMorphismData}
  {g_X g_Y : ℤ}
-- given
  (h_gX : f.deg_KX = 2 * g_X - 2)
  (h_gY : f.deg_KY = 2 * g_Y - 2)
  (h_decomp : f.deg_KX = f.degree * f.deg_KY + f.deg_R) :
-- imply
  2 * g_X - 2 ≥ f.degree * (2 * g_Y - 2) := by
-- proof
  have := riemann_hurwitz_genus_from_data f g_X g_Y h_gX h_gY h_decomp
  linarith [f.h_deg_R_nonneg]

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_ramification_determines_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_ramification_determines_genus
  {f : CurveMorphismData}
-- given
  (h_decomp : f.deg_KX = f.degree * f.deg_KY + f.deg_R) :
-- imply
  f.deg_R = f.deg_KX - f.degree * f.deg_KY := by
-- proof
  linarith [h_decomp]

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_P1_target](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_P1_target
  {n deg_KX deg_R : ℤ}
-- given
  (h_nonneg : 0 ≤ deg_R)
  (h_pos : 0 < n)
  (h_formula : deg_KX = -2 * n + deg_R) :
-- imply
  (CurveMorphismData.toP1 n deg_KX deg_R h_nonneg h_pos).deg_KX = -2 * (CurveMorphismData.toP1 n deg_KX deg_R h_nonneg h_pos).degree + (CurveMorphismData.toP1 n deg_KX deg_R h_nonneg h_pos).deg_R := by
-- proof
  simp [CurveMorphismData.toP1]
  linarith

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_P1_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_P1_genus
  {n g deg_R : ℤ}
-- given
  (h_RH : 2 * g - 2 = -2 * n + deg_R) :
-- imply
  deg_R = 2 * g + 2 * n - 2 := by
-- proof
linarith

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[totally_ramified_P1_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma totally_ramified_P1_genus
  {n g r : ℤ}
-- given
  (h_RH : 2 * g - 2 = -2 * n + r * (n - 1)) :
-- imply
  2 * g = r * (n - 1) - 2 * n + 2 := by
-- proof
linarith
section EllipticCurveExample

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[elliptic_curve_canonical_degree_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma elliptic_curve_canonical_degree_zero
-- imply
  let n : ℤ := 2 let num_ram : ℤ := 4 let e : ℤ := 2 let deg_R := num_ram * (e - 1) let deg_KP1 : ℤ := -2 n * deg_KP1 + deg_R = 0 := by
-- proof
norm_num

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[elliptic_curve_genus_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma elliptic_curve_genus_one
-- imply
  let n : ℤ := 2 let deg_R : ℤ := 4 * (2 - 1) let g : ℤ := 1 2 * g - 2 = n * (-2) + deg_R := by
-- proof
norm_num

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[ellipticCurveP1_satisfies_RH](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma ellipticCurveP1_satisfies_RH
-- imply
  ellipticCurveP1Data.deg_KX = ellipticCurveP1Data.degree * ellipticCurveP1Data.deg_KY + ellipticCurveP1Data.deg_R := by
-- proof
  simp [ellipticCurveP1Data]

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[ellipticCurve_genus_from_canonical](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma ellipticCurve_genus_from_canonical
-- imply
  (0 : ℤ) = 2 * 1 - 2 := by
-- proof
norm_num
section Hyperelliptic

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[hyperelliptic_branch_points_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma hyperelliptic_branch_points_eq
  {g : ℤ}
  {b : ℤ}
-- given
  (h_RH : 2 * g - 2 = 2 * (-2 : ℤ) + b) :
-- imply
  b = 2 * g + 2 := by
-- proof
linarith

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[hyperellipticData_satisfies_RH](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma hyperellipticData_satisfies_RH
  {g : ℤ}
-- given
  (hg : 0 ≤ 2 * g + 2) :
-- imply
  (hyperellipticData g hg).deg_KX = (hyperellipticData g hg).degree * (hyperellipticData g hg).deg_KY + (hyperellipticData g hg).deg_R := by
-- proof
  simp [hyperellipticData]
  ring

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_arithmetic_genus_constraint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_arithmetic_genus_constraint
  {g_X g_Y : ℕ}
  {n deg_R : ℤ}
-- given
  (h_formula : 2 * (g_X : ℤ) - 2 = n * (2 * (g_Y : ℤ) - 2) + deg_R) :
-- imply
  deg_R = 2 * (g_X : ℤ) - 2 - n * (2 * (g_Y : ℤ) - 2) := by
-- proof
linarith

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_genus_growth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_genus_growth
  {g_X g_Y : ℤ}
  {n deg_R : ℤ}
-- given
  (hR : 0 ≤ deg_R)
  (h_formula : 2 * g_X - 2 = n * (2 * g_Y - 2) + deg_R) :
-- imply
  g_X ≥ n * (g_Y - 1) + 1 := by
-- proof
linarith

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_isomorphism_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_isomorphism_genus
  {g_X g_Y : ℤ}
-- given
  (h_formula : 2 * g_X - 2 = 1 * (2 * g_Y - 2) + 0) :
-- imply
  g_X = g_Y := by
-- proof
linarith

end RiemannHurwitzFormula

namespace RiemannHurwitzFormula

/--
[riemann_hurwitz_etale_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RiemannHurwitzFormula.lean)
-/
@[path]
lemma riemann_hurwitz_etale_genus
  {g_X g_Y n : ℤ}
-- given
  (h_formula : 2 * g_X - 2 = n * (2 * g_Y - 2) + 0) :
-- imply
  g_X = n * g_Y - n + 1 := by
-- proof
linarith
end RiemannHurwitzFormula



-- created on 2026-10-23
