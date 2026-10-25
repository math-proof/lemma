import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalFixedDensityPerron.Part9
open StatMech StatMech.FrontierD


/--
[sixVertexCanonicalFixedEvenDensityFloor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedEvenDensityFloor_pos_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexCanonicalFixedEvenDensityFloor hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedEvenDensityFloor_pos hc s

/--
[eventually_exists_sixVertexCanonicalFixedEvenDensityWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma eventually_exists_sixVertexCanonicalFixedEvenDensityWitness_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, ∃ p, SixVertexCanonicalFixedEvenDensityWitness hc s k p := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexCanonicalFixedEvenDensityWitness hc s

/--
[eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, SixVertexCanonicalFixedEvenDensityWitness hc s k (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedEvenDensityPerronBetheRoots_witness hc s

/--
[sixVertexCanonicalFixedOddDensityFloor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma sixVertexCanonicalFixedOddDensityFloor_pos_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexCanonicalFixedOddDensityFloor hc s := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalFixedOddDensityFloor_pos hc s

/--
[eventually_exists_sixVertexCanonicalFixedOddDensityWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma eventually_exists_sixVertexCanonicalFixedOddDensityWitness_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, ∃ p, SixVertexCanonicalFixedOddDensityWitness hc s k p := by
-- proof
  apply StatMech.FrontierD.eventually_exists_sixVertexCanonicalFixedOddDensityWitness hc s

/--
[eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, SixVertexCanonicalFixedOddDensityWitness hc s k (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedOddDensityPerronBetheRoots_witness hc s

/--
[sixVertexWeightedFiniteDensityGauge_le_invWidth_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_le_invWidth_of_lower_eq
  {c : Real}
  {N q r : Nat}
  {p : Fin q -> Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hq : 0 < q)
  (hcharge : N = 2 * q + 2 * r)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N q p)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N q p x) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc N q p (sixVertexFourierPhysicalDensityMap hc) <= sixVertexFixedChargeDensityInvWidthConstantOfLower c r lower / N := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_le_invWidth_of_lower hc hN hq hcharge hopen hsol hlower hdensity

/--
[eventually_sixVertexCanonicalFixedEvenDensityGauge_le_invWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedEvenDensityGauge_le_invWidth_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s) k) ((s + k + 1) + (s + k + 1)) (sixVertexCanonicalFixedEvenDensityPerronBetheRoots hc s k) (sixVertexFourierPhysicalDensityMap hc) <= sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s) (sixVertexCanonicalFixedEvenDensityFloor hc s) / sixVertexFourWidth (2 * s) k := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedEvenDensityGauge_le_invWidth hc s

/--
[eventually_sixVertexCanonicalFixedOddDensityGauge_le_invWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalFixedOddDensityGauge_le_invWidth_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth (2 * s + 1) k) (((s + k + 1) + 1) + (s + k + 1)) (sixVertexCanonicalFixedOddDensityPerronBetheRoots hc s k) (sixVertexFourierPhysicalDensityMap hc) <= sixVertexFixedChargeDensityInvWidthConstantOfLower c (2 * s + 1) (sixVertexCanonicalFixedOddDensityFloor hc s) / sixVertexFourWidth (2 * s + 1) k := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalFixedOddDensityGauge_le_invWidth hc s

/--
[sixVertexCanonicalHalfDensityFloor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma sixVertexCanonicalHalfDensityFloor_pos_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexCanonicalHalfDensityFloor hc := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalHalfDensityFloor_pos hc

/--
[eventually_sixVertexCanonicalHalfDensityFloor_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalHalfDensityFloor_le_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, forall x, sixVertexCanonicalHalfDensityFloor hc <= sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc k) x := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalHalfDensityFloor_le hc

/--
[sixVertexWeightedFiniteDensityGauge_le_invWidth_of_half_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma sixVertexWeightedFiniteDensityGauge_le_invWidth_of_half_lower_eq
  {c : Real}
  {N q : Nat}
  {p : Fin q -> Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hq : 0 < q)
  (hhalf : N = 2 * q)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N q p)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N q p x) :
-- imply
  sixVertexWeightedFiniteDensityGauge hc N q p (sixVertexFourierPhysicalDensityMap hc) <= sixVertexHalfDensityInvWidthConstantOfLower c lower / N := by
-- proof
  apply StatMech.FrontierD.sixVertexWeightedFiniteDensityGauge_le_invWidth_of_half_lower hc hN hq hhalf hopen hsol hlower hdensity

/--
[eventually_sixVertexCanonicalHalfDensityGauge_le_invWidth](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalFixedDensityPerron.lean)
-/
@[path]
private lemma eventually_sixVertexCanonicalHalfDensityGauge_le_invWidth_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ∀ᶠ k : Nat in atTop, sixVertexWeightedFiniteDensityGauge hc (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc k) (sixVertexFourierPhysicalDensityMap hc) <= sixVertexHalfDensityInvWidthConstantOfLower c (sixVertexCanonicalHalfDensityFloor hc) / sixVertexFourWidth 0 k := by
-- proof
  apply StatMech.FrontierD.eventually_sixVertexCanonicalHalfDensityGauge_le_invWidth hc


-- created on 2026-10-23
