import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalDivisorDecomposition.Part4
open Ideal Module CanonicalSheafCurves
open CanonicalSheafCurves


/--
[globalRamification_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma globalRamification_eq
  [CommRing R]
  [IsDedekindDomain R]
  {basePrimes : Finset (Ideal R)}
-- given
  (hmax : ∀ p ∈ basePrimes, p.IsMaximal)
  (hbot : ∀ p ∈ basePrimes, p ≠ ⊥) :
-- imply
  globalRamification S basePrimes hmax hbot = basePrimes.sum fun p => if h : p ∈ basePrimes then haveI : p.IsMaximal :=
-- proof
  hmax p h
    totalRamificationAt S p (hbot p h)
    else 0 := rfl

/--
[globalRamification_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma globalRamification_nonneg
  [CommRing R]
  [IsDedekindDomain R]
  {basePrimes : Finset (Ideal R)}
-- given
  (hmax : ∀ p ∈ basePrimes, p.IsMaximal)
  (hbot : ∀ p ∈ basePrimes, p ≠ ⊥) :
-- imply
  0 ≤ globalRamification S basePrimes hmax hbot := by
-- proof
  unfold globalRamification
  apply Finset.sum_nonneg
  intro p hp
  simp [hp]
  haveI : p.IsMaximal := hmax p hp
  exact totalRamificationAt_nonneg S (hbot p hp)

/--
[CurveCovering.deg_R_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.deg_R_nonneg
  {f : CurveCovering} :
-- imply
  0 ≤ f.deg_R :=
-- proof
  globalRamification_nonneg f.S f.basePrimes f.h_max f.h_bot

/--
[CurveCovering.degK_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.degK_eq
  {f : CurveCovering} :
-- imply
  f.X.degK = f.n * f.Y.degK + f.deg_R := by
-- proof
  rw [f.h_degK_X_sum]
  have h_sum : f.basePrimes.sum f.localDegK_X =
    f.basePrimes.sum (fun p =>
      f.n * f.localDegK_Y p +
        (if h : p ∈ f.basePrimes then
          haveI : p.IsMaximal := f.h_max p h
          totalRamificationAt f.S p (f.h_bot p h)
        else 0)) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact f.h_local_degree p hp
  rw [h_sum]
  rw [Finset.sum_add_distrib]
  have h_mul : f.basePrimes.sum (fun p => f.n * f.localDegK_Y p) =
    f.n * f.basePrimes.sum f.localDegK_Y := by
    rw [Finset.mul_sum]
  rw [h_mul]
  rw [← f.h_degK_Y_sum]
  rfl
section GenusFormula
variable (f : CurveCovering)

/--
[CurveCovering.riemann_hurwitz_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.riemann_hurwitz_genus
  {f : CurveCovering} :
-- imply
  2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R := by
-- proof
  have hX := deg_canonical_eq_2g_sub_2 f.X
  have hY := deg_canonical_eq_2g_sub_2 f.Y
  have hd := f.degK_eq
  rw [hX, hY] at hd
  linarith

/--
[CurveCovering.genus_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.genus_lower_bound
  {f : CurveCovering} :
-- imply
  f.X.g ≥ f.n * (f.Y.g - 1) + 1 := by
-- proof
  have hRH := f.riemann_hurwitz_genus
  have hR := f.deg_R_nonneg
  nlinarith

/--
[CurveCovering.deg_R_from_genera](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.deg_R_from_genera
  {f : CurveCovering} :
-- imply
  f.deg_R = 2 * f.X.g - 2 - f.n * (2 * f.Y.g - 2) := by
-- proof
  linarith [f.riemann_hurwitz_genus]

/--
[CurveCovering.via_riemann_hurwitz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.via_riemann_hurwitz
  {f : CurveCovering} :
-- imply
  2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R :=
-- proof
  riemann_hurwitz_formula f.n f.X.g f.Y.g f.deg_R f.X.degK f.Y.degK
    (f.n * f.Y.degK)
    (deg_canonical_eq_2g_sub_2 f.X)
    (deg_canonical_eq_2g_sub_2 f.Y)
    rfl
    f.degK_eq
end GenusFormula
section Etale
variable (f : CurveCovering)

/--
[CurveCovering.etale_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.etale_genus
  {f : CurveCovering}
-- given
  (h : f.deg_R = 0) :
-- imply
  2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) := by
-- proof
  linarith [f.riemann_hurwitz_genus]

/--
[CurveCovering.etale_genus_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.etale_genus_exact
  {f : CurveCovering}
-- given
  (h : f.deg_R = 0) :
-- imply
  f.X.g = f.n * (f.Y.g - 1) + 1 := by
-- proof
  have h1 := f.etale_genus h
  nlinarith

/--
[CurveCovering.etale_double_cover_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.etale_double_cover_genus
  {f : CurveCovering}
-- given
  (h_etale : f.deg_R = 0)
  (h_double : f.n = 2) :
-- imply
  f.X.g = 2 * f.Y.g - 1 := by
-- proof
  have h1 := f.etale_genus_exact h_etale
  rw [h_double] at h1
  linarith
end Etale
section Specializations

/--
[hyperelliptic_identity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma hyperelliptic_identity
  {g : ℤ} :
-- imply
  2 * g - 2 = 2 * (2 * 0 - 2) + (2 * g + 2) := by
-- proof
ring

/--
[CurveCovering.ellipticIdentity_deg_R](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.ellipticIdentity_deg_R
-- imply
  CurveCovering.ellipticIdentity.deg_R = 0 := by
-- proof
  unfold CurveCovering.deg_R globalRamification CurveCovering.ellipticIdentity
  simp

/--
[CurveCovering.ellipticIdentity_degK_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.ellipticIdentity_degK_eq
-- imply
  CurveCovering.ellipticIdentity.X.degK = CurveCovering.ellipticIdentity.n * CurveCovering.ellipticIdentity.Y.degK + CurveCovering.ellipticIdentity.deg_R :=
-- proof
  CurveCovering.ellipticIdentity.degK_eq

/--
[CurveCovering.ellipticIdentity_rh_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.ellipticIdentity_rh_genus
-- imply
  2 * CurveCovering.ellipticIdentity.X.g - 2 = CurveCovering.ellipticIdentity.n * (2 * CurveCovering.ellipticIdentity.Y.g - 2) + CurveCovering.ellipticIdentity.deg_R :=
-- proof
  CurveCovering.ellipticIdentity.riemann_hurwitz_genus

/--
[CurveCovering.ellipticIdentity_genus_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.ellipticIdentity_genus_bound
-- imply
  CurveCovering.ellipticIdentity.X.g ≥ CurveCovering.ellipticIdentity.n * (CurveCovering.ellipticIdentity.Y.g - 1) + 1 :=
-- proof
  CurveCovering.ellipticIdentity.genus_lower_bound

/--
[CurveCovering.ellipticIdentity_values](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.ellipticIdentity_values
-- imply
  CurveCovering.ellipticIdentity.X.g = 1 ∧ CurveCovering.ellipticIdentity.Y.g = 1 ∧ CurveCovering.ellipticIdentity.n = 1 ∧ CurveCovering.ellipticIdentity.deg_R = 0 := by
-- proof
  refine ⟨rfl, rfl, rfl, ?_⟩
  exact CurveCovering.ellipticIdentity_deg_R

/--
[CurveCovering.identityCovering_deg_R](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.identityCovering_deg_R
  {C : SmoothCompleteCurve}
  {p : Ideal ℤ}
-- given
  (hp_max : p.IsMaximal)
  (hp_bot : p ≠ ⊥)
  (h_totalRam : totalRamificationAt ℤ p hp_bot = 0) :
-- imply
  (CurveCovering.identityCovering C p hp_max hp_bot h_totalRam).deg_R = 0 := by
-- proof
  unfold CurveCovering.deg_R globalRamification CurveCovering.identityCovering
  simp [h_totalRam]

/--
[CurveCovering.identityCovering_rh_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCovering.identityCovering_rh_genus
  {C : SmoothCompleteCurve}
  {p : Ideal ℤ}
-- given
  (hp_max : p.IsMaximal)
  (hp_bot : p ≠ ⊥)
  (h_totalRam : totalRamificationAt ℤ p hp_bot = 0) :
-- imply
  2 * C.g - 2 = 1 * (2 * C.g - 2) + (CurveCovering.identityCovering C p hp_max hp_bot h_totalRam).deg_R :=
-- proof
  (CurveCovering.identityCovering C p hp_max hp_bot h_totalRam).riemann_hurwitz_genus
section DirectCovering

/--
[CurveCoveringDirect.deg_R_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCoveringDirect.deg_R_nonneg
  {f : CurveCoveringDirect} :
-- imply
  0 ≤ f.deg_R :=
-- proof
  globalRamification_nonneg f.S f.basePrimes f.h_max f.h_bot

/--
[CurveCoveringDirect.degK_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCoveringDirect.degK_eq
  {f : CurveCoveringDirect} :
-- imply
  f.X.degK = f.n * f.Y.degK + f.deg_R :=
-- proof
  f.h_degK_formula

/--
[CurveCoveringDirect.riemann_hurwitz_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCoveringDirect.riemann_hurwitz_genus
  {f : CurveCoveringDirect} :
-- imply
  2 * f.X.g - 2 = f.n * (2 * f.Y.g - 2) + f.deg_R := by
-- proof
  have hX := deg_canonical_eq_2g_sub_2 f.X
  have hY := deg_canonical_eq_2g_sub_2 f.Y
  have hF := f.degK_eq
  rw [hX, hY] at hF
  linarith

/--
[CurveCoveringDirect.deg_R_from_genera](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCoveringDirect.deg_R_from_genera
  {f : CurveCoveringDirect} :
-- imply
  f.deg_R = 2 * f.X.g - 2 - f.n * (2 * f.Y.g - 2) := by
-- proof
  linarith [f.riemann_hurwitz_genus]

/--
[CurveCoveringDirect.genus_lower_bound](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCoveringDirect.genus_lower_bound
  {f : CurveCoveringDirect} :
-- imply
  f.X.g ≥ f.n * (f.Y.g - 1) + 1 := by
-- proof
  nlinarith [f.riemann_hurwitz_genus, f.deg_R_nonneg, f.h_n_pos]

/--
[CurveCoveringDirect.etale_genus_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCoveringDirect.etale_genus_exact
  {f : CurveCoveringDirect}
-- given
  (h : f.deg_R = 0) :
-- imply
  f.X.g = f.n * (f.Y.g - 1) + 1 := by
-- proof
  nlinarith [f.riemann_hurwitz_genus]

/--
[CurveCoveringDirect.etale_double_cover_genus](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalDivisorDecomposition.lean)
-/
@[path]
lemma CurveCoveringDirect.etale_double_cover_genus
  {f : CurveCoveringDirect}
-- given
  (h_etale : f.deg_R = 0)
  (h_double : f.n = 2) :
-- imply
  f.X.g = 2 * f.Y.g - 1 := by
-- proof
  have h1 := f.etale_genus_exact h_etale
  rw [h_double] at h1
  linarith


-- created on 2026-10-23
