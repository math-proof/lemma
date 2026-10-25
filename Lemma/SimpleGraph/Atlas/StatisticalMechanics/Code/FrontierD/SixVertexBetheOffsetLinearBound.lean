import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetLinearBound
open StatMech StatMech.FrontierD


/--
[lower_mul_abs_sub_le_abs_intervalIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLinearBound.lean)
-/
@[path]
private lemma lower_mul_abs_sub_le_abs_intervalIntegral_eq
  {rho : Real → Real}
  {lower a b : Real}
-- given
  (hrho : Continuous rho)
  (hlower : ∀ x, lower ≤ rho x)
  (hlowerNonneg : 0 ≤ lower) :
-- imply
  lower * |b - a| ≤ |∫ x in a..b, rho x| := by
-- proof
  apply StatMech.FrontierD.lower_mul_abs_sub_le_abs_intervalIntegral hrho hlower hlowerNonneg

/--
[abs_intervalIntegral_sub_const_mul_le_of_lipschitz](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLinearBound.lean)
-/
@[path]
private lemma abs_intervalIntegral_sub_const_mul_le_of_lipschitz_eq
  {f : Real → Real}
  {C : NNReal}
  {a b u : Real}
-- given
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hab : a ≤ b)
  (hu : u ∈ Set.Icc a b) :
-- imply
  |(∫ x in a..b, f x) - f u * (b - a)| ≤ (C : Real) * (b - a) ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_intervalIntegral_sub_const_mul_le_of_lipschitz hf hlip hab hu

/--
[abs_sixVertexBetheCountingFunction_midpoint_defect_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLinearBound.lean)
-/
@[path]
private lemma abs_sixVertexBetheCountingFunction_midpoint_defect_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {a b : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n ≤ N)
  (hab : a ≤ b) :
-- imply
  |(sixVertexBetheCountingFunction c N n p a + sixVertexBetheCountingFunction c N n p b) / 2 - sixVertexBetheCountingFunction c N n p ((a + b) / 2)| ≤ (sixVertexFiniteRootDensityLipschitzConstant c : Real) * (b - a) ^ 2 / 4 := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheCountingFunction_midpoint_defect_le hc hN hn p hab

/--
[abs_sixVertexBetheCountingFunction_sub_le_mul_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLinearBound.lean)
-/
@[path]
private lemma abs_sixVertexBetheCountingFunction_sub_le_mul_abs_eq
  {c : Real}
  {N np nq : Nat}
  {p : Fin np → Real}
  {q : Fin nq → Real}
  {rho : Real → Real}
  {EP EQ : Real}
  {x : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hpSymm : SixVertexRootSymmetric p)
  (hqSymm : SixVertexRootSymmetric q)
  (hEP : 0 ≤ EP)
  (hEQ : 0 ≤ EQ)
  (hpClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c N np p y - rho y)| ≤ EP / N)
  (hqClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c N nq q y - rho y)| ≤ EQ / N)
  (hx : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |sixVertexBetheCountingFunction c N np p x - sixVertexBetheCountingFunction c N nq q x| ≤ (((EP + EQ) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / N) * |x| := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheCountingFunction_sub_le_mul_abs hc hN hpSymm hqSymm hEP hEQ hpClose hqClose hx

/--
[abs_alignedBetheRootOffset_le_mul_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLinearBound.lean)
-/
@[path]
private lemma abs_alignedBetheRootOffset_le_mul_abs_eq
  {c : Real}
  {N np nq : Nat}
  {p : Fin np → Real}
  {q : Fin nq → Real}
  {rho : Real → Real}
  {EP EQ lower : Real}
  {i : Fin np}
  {j : Fin nq}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hpOpen : SixVertexOpenRootSimplex p)
  (hqOpen : SixVertexOpenRootSimplex q)
  (hpSol : SixVertexSatisfiesBetheEquations c N np p)
  (hqSol : SixVertexSatisfiesBetheEquations c N nq q)
  (hEP : 0 ≤ EP)
  (hEQ : 0 ≤ EQ)
  (hlower : 0 < lower)
  (hqLower : ∀ x, lower ≤ sixVertexFiniteRootDensity c N nq q x)
  (hpClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c N np p y - rho y)| ≤ EP / N)
  (hqClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c N nq q y - rho y)| ≤ EQ / N)
  (hquantum : sixVertexCentralQuantumNumber i = sixVertexCentralQuantumNumber j) :
-- imply
  |(N : Real) * (q j - p i)| ≤ ((EP + EQ) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / lower * |p i| := by
-- proof
  apply StatMech.FrontierD.abs_alignedBetheRootOffset_le_mul_abs hc hN hpOpen hqOpen hpSol hqSol hEP hEQ hlower hqLower hpClose hqClose i j hquantum

/--
[abs_sixVertexEvenChargeBetheOffset_le_mul_abs_halfRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLinearBound.lean)
-/
@[path]
private lemma abs_sixVertexEvenChargeBetheOffset_le_mul_abs_halfRoot_eq
  {c : Real}
  {s k : Nat}
  {rho : Real → Real}
  {EP EQ lower : Real}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c)
  (hEP : 0 ≤ EP)
  (hEQ : 0 ≤ EQ)
  (hlower : 0 < lower)
  (hfixedLower : ∀ x, lower ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) x)
  (hhalfClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) ((2 * s + k + 1) + (2 * s + k + 1)) (sixVertexHalfFilledBetheRoots hc (2 * s + k)) y - rho y)| ≤ EP / sixVertexFourWidth (2 * s) k)
  (hfixedClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) (sixVertexFixedChargeBetheRoots hc (2 * s) k) y - rho y)| ≤ EQ / sixVertexFourWidth (2 * s) k) :
-- imply
  |sixVertexEvenChargeBetheOffset hc s k j| ≤ ((EP + EQ) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / lower * |sixVertexHalfFilledBetheRoots hc (2 * s + k) (sixVertexEvenChargeHalfIndex s k j)| := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexEvenChargeBetheOffset_le_mul_abs_halfRoot hc s k hEP hEQ hlower hfixedLower hhalfClose hfixedClose j

/--
[abs_sixVertexOddChargeBetheOffset_le_mul_abs_halfAverage_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetLinearBound.lean)
-/
@[path]
private lemma abs_sixVertexOddChargeBetheOffset_le_mul_abs_halfAverage_add_eq
  {c : Real}
  {s k : Nat}
  {rho : Real → Real}
  {EP EQ lowerP lowerQ : Real}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c)
  (hEP : 0 ≤ EP)
  (hEQ : 0 ≤ EQ)
  (hlowerP : 0 < lowerP)
  (hlowerQ : 0 < lowerQ)
  (hhalfLower : ∀ x, lowerP ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) x)
  (hfixedLower : ∀ x, lowerQ ≤ sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) x)
  (hhalfClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k)) y - rho y)| ≤ EP / sixVertexFourWidth (2 * s + 1) k)
  (hfixedClose : ∀ y ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c y * (sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k) y - rho y)| ≤ EQ / sixVertexFourWidth (2 * s + 1) k) :
-- imply
  |sixVertexOddChargeBetheOffset hc s k j| ≤ ((EP + EQ) / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) / lowerQ * |(sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) (sixVertexOddChargeLowerHalfIndex s k j) + sixVertexHalfFilledBetheRoots hc (2 * s + 1 + k) (sixVertexOddChargeUpperHalfIndex s k j)) / 2| + (sixVertexFiniteRootDensityLipschitzConstant c : Real) / (4 * lowerP ^ 2 * lowerQ * sixVertexFourWidth (2 * s + 1) k) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexOddChargeBetheOffset_le_mul_abs_halfAverage_add hc s k hEP hEQ hlowerP hlowerQ hhalfLower hfixedLower hhalfClose hfixedClose j


-- created on 2026-10-23
