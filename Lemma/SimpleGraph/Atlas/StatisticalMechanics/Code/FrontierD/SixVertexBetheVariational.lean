import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheVariational
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexBetheIntegratingFactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexBetheIntegratingFactor_pos_eq
  {c : ℝ}
  {x : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexBetheIntegratingFactor c x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheIntegratingFactor_pos hc x

/--
[sixVertexThetaDerivativeDenominator_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_swap_eq
  {c x y : ℝ} :
-- imply
  sixVertexThetaDerivativeDenominator c y x = sixVertexThetaDerivativeDenominator c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_swap c x y

/--
[sixVertexThetaDerivativeDenominator_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexThetaDerivativeDenominator_pos_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexThetaDerivativeDenominator c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexThetaDerivativeDenominator_pos hc x y

/--
[hasDerivAt_sixVertexTheta_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexTheta_right_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  HasDerivAt (fun t => sixVertexTheta c x t) (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x / sixVertexThetaDerivativeDenominator c x y) y := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexTheta_right hc x y

/--
[hasFDerivAt_sixVertexTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma hasFDerivAt_sixVertexTheta_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  HasFDerivAt (fun xy : ℝ × ℝ => sixVertexTheta c xy.1 xy.2) (sixVertexThetaFDeriv c x y) (x, y) := by
-- proof
  apply StatMech.FrontierD.hasFDerivAt_sixVertexTheta hc x y

/--
[sixVertexBetheResidual_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexBetheResidual_eq_zero_iff_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ} :
-- imply
  (∀ j, sixVertexBetheResidual c N n p j = 0) ↔ SixVertexSatisfiesBetheEquations c N n p := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheResidual_eq_zero_iff c N n p

/--
[sixVertexNormalizedBetheResidual_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexNormalizedBetheResidual_eq_zero_iff_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hc : 2 < c) :
-- imply
  (∀ j, sixVertexNormalizedBetheResidual c N n p j = 0) ↔ SixVertexSatisfiesBetheEquations c N n p := by
-- proof
  apply StatMech.FrontierD.sixVertexNormalizedBetheResidual_eq_zero_iff hc N n p

/--
[sixVertexTheta_mixed_integratingFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexTheta_mixed_integratingFactor_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x / sixVertexThetaDerivativeDenominator c x y) / sixVertexBetheIntegratingFactor c x = (-4 * sixVertexDelta c) / sixVertexThetaDerivativeDenominator c x y := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_mixed_integratingFactor hc x y

/--
[sixVertexTheta_mixed_integratingFactor_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexTheta_mixed_integratingFactor_symm_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c x / sixVertexThetaDerivativeDenominator c x y) / sixVertexBetheIntegratingFactor c x = (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c y / sixVertexThetaDerivativeDenominator c y x) / sixVertexBetheIntegratingFactor c y := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_mixed_integratingFactor_symm hc x y

/--
[hasFDerivAt_sixVertexNormalizedTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma hasFDerivAt_sixVertexNormalizedTheta_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  HasFDerivAt (fun xy : ℝ × ℝ => sixVertexNormalizedTheta c xy.1 xy.2) (fderiv ℝ (fun xy : ℝ × ℝ => sixVertexNormalizedTheta c xy.1 xy.2) (x, y)) (x, y) := by
-- proof
  apply StatMech.FrontierD.hasFDerivAt_sixVertexNormalizedTheta hc x y

/--
[differentiable_sixVertexNormalizedTheta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma differentiable_sixVertexNormalizedTheta_eq
  {c : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  Differentiable ℝ (fun xy : ℝ × ℝ => sixVertexNormalizedTheta c xy.1 xy.2) := by
-- proof
  apply StatMech.FrontierD.differentiable_sixVertexNormalizedTheta hc

/--
[hasDerivAt_sixVertexNormalizedTheta_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexNormalizedTheta_right_eq
  {c : ℝ}
  {x y : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  HasDerivAt (fun t => sixVertexNormalizedTheta c x t) ((-4 * sixVertexDelta c) / sixVertexThetaDerivativeDenominator c x y) y := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexNormalizedTheta_right hc x y

/--
[differentiable_sixVertexBethePairOneForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma differentiable_sixVertexBethePairOneForm_eq
  {c : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  Differentiable ℝ (sixVertexBethePairOneForm c) := by
-- proof
  apply StatMech.FrontierD.differentiable_sixVertexBethePairOneForm hc

/--
[fderiv_sixVertexBethePairOneForm_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma fderiv_sixVertexBethePairOneForm_symmetric_eq
  {c : ℝ}
  {xy u v : ℝ × ℝ}
-- given
  (hc : 2 < c) :
-- imply
  fderiv ℝ (sixVertexBethePairOneForm c) xy u v = fderiv ℝ (sixVertexBethePairOneForm c) xy v u := by
-- proof
  apply StatMech.FrontierD.fderiv_sixVertexBethePairOneForm_symmetric hc xy u v

/--
[exists_sixVertexBethePairPotential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma exists_sixVertexBethePairPotential_eq
  {c : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  ∃ H : (ℝ × ℝ) → ℝ, ∀ xy, HasFDerivAt H (sixVertexBethePairOneForm c xy) xy := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexBethePairPotential hc

/--
[hasFDerivAt_sixVertexBethePairPotential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma hasFDerivAt_sixVertexBethePairPotential_eq
  {c : ℝ}
  {xy : ℝ × ℝ}
-- given
  (hc : 2 < c) :
-- imply
  HasFDerivAt (sixVertexBethePairPotential hc) (sixVertexBethePairOneForm c xy) xy := by
-- proof
  apply StatMech.FrontierD.hasFDerivAt_sixVertexBethePairPotential hc xy

/--
[continuous_sixVertexBetheOneBodyCoefficient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma continuous_sixVertexBetheOneBodyCoefficient_eq
  {c : ℝ}
  {N : ℕ}
  {I : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  Continuous (sixVertexBetheOneBodyCoefficient c N I) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBetheOneBodyCoefficient hc N I

/--
[hasDerivAt_sixVertexBetheOneBodyPotential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexBetheOneBodyPotential_eq
  {c : ℝ}
  {N : ℕ}
  {I x : ℝ}
-- given
  (hc : 2 < c) :
-- imply
  HasDerivAt (sixVertexBetheOneBodyPotential c N I) (sixVertexBetheOneBodyCoefficient c N I x) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexBetheOneBodyPotential hc N I x

/--
[hasFDerivAt_sixVertexBethePotential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma hasFDerivAt_sixVertexBethePotential_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hc : 2 < c) :
-- imply
  HasFDerivAt (sixVertexBethePotential hc N n) (sixVertexBetheOneForm hc N n p) p := by
-- proof
  apply StatMech.FrontierD.hasFDerivAt_sixVertexBethePotential hc N n p

/--
[sixVertexBetheOneForm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexBetheOneForm_apply_eq
  {c : ℝ}
  {N n : ℕ}
  {p v : Fin n → ℝ}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheOneForm hc N n p v = ∑ j, sixVertexNormalizedBetheResidual c N n p j * v j := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheOneForm_apply hc N n p v

/--
[sixVertexBetheResidual_eq_updateSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexBetheResidual_eq_updateSub_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
  {j : Fin n}
-- given
  (hN : 0 < N) :
-- imply
  sixVertexBetheResidual c N n p j = (N : ℝ) * (p j - sixVertexBetheUpdate c N n p j) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheResidual_eq_updateSub hN p j

/--
[sixVertexBetheOneForm_updateSub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexBetheOneForm_updateSub_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hc : 2 < c)
  (hN : 0 < N) :
-- imply
  sixVertexBetheOneForm hc N n p (sixVertexBetheUpdate c N n p - p) = -(N : ℝ) * ∑ j, (sixVertexBetheUpdate c N n p j - p j) ^ 2 / sixVertexBetheIntegratingFactor c (p j) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheOneForm_updateSub hc hN p

/--
[sixVertexBetheOneForm_updateSub_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexBetheOneForm_updateSub_neg_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hne : sixVertexBetheUpdate c N n p ≠ p) :
-- imply
  sixVertexBetheOneForm hc N n p (sixVertexBetheUpdate c N n p - p) < 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheOneForm_updateSub_neg hc hN p hne

/--
[continuous_sixVertexBethePotential](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma continuous_sixVertexBethePotential_eq
  {c : ℝ}
  {N n : ℕ}
-- given
  (hc : 2 < c) :
-- imply
  Continuous (sixVertexBethePotential hc N n) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBethePotential hc N n

/--
[exists_sixVertexBetheUpdate_fixedPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma exists_sixVertexBetheUpdate_fixedPoint_eq
  {c : ℝ}
  {N n : ℕ}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hhalf : 2 * n ≤ N) :
-- imply
  ∃ p : Fin n → ℝ, SixVertexClosedRootSimplex p ∧ sixVertexBetheUpdate c N n p = p := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexBetheUpdate_fixedPoint hc hN hhalf

/--
[exists_sixVertexBetheSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma exists_sixVertexBetheSolution_eq
  {c : ℝ}
  {N n : ℕ}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N) :
-- imply
  ∃ p : Fin n → ℝ, SixVertexOpenRootSimplex p ∧ SixVertexSatisfiesBetheEquations c N n p := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexBetheSolution hc hhalf

/--
[sixVertexChosenBetheSolution_mem_open](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexChosenBetheSolution_mem_open_eq
  {c : ℝ}
  {N n : ℕ}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N) :
-- imply
  SixVertexOpenRootSimplex (sixVertexChosenBetheSolution hc hhalf) := by
-- proof
  apply StatMech.FrontierD.sixVertexChosenBetheSolution_mem_open hc hhalf

/--
[sixVertexChosenBetheSolution_is_solution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexChosenBetheSolution_is_solution_eq
  {c : ℝ}
  {N n : ℕ}
-- given
  (hc : 2 < c)
  (hhalf : 2 * n ≤ N) :
-- imply
  SixVertexSatisfiesBetheEquations c N n (sixVertexChosenBetheSolution hc hhalf) := by
-- proof
  apply StatMech.FrontierD.sixVertexChosenBetheSolution_is_solution hc hhalf

/--
[sixVertexBetheSolution_quantumSpacing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexBetheSolution_quantumSpacing_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin n → ℝ}
  {i j : Fin n}
-- given
  (hc : 2 < c)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N n p)
  (hij : i < j) :
-- imply
  2 * Real.pi * (sixVertexCentralQuantumNumber j - sixVertexCentralQuantumNumber i) < (N : ℝ) * (p j - p i) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_quantumSpacing hc hopen hsol hij

/--
[sixVertexBetheSolution_adjacentSpacing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheVariational.lean)
-/
@[path]
private lemma sixVertexBetheSolution_adjacentSpacing_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hopen : SixVertexOpenRootSimplex p)
  (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) :
-- imply
  2 * Real.pi < (N : ℝ) * (p i.succ - p i.castSucc) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheSolution_adjacentSpacing hc hopen hsol i


-- created on 2026-10-23
