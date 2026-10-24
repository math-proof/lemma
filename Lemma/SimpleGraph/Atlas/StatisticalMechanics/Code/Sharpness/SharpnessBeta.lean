import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.SharpnessBeta
open MeasureTheory Set Filter Topology Real StatMech StatMech.Sharpness


/--
[pBeta_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean)
-/
@[path]
private lemma pBeta_lt_one_eq
  {d : ℕ}
  {J β : ℝ} :
-- imply
  pBeta J β < 1 := by
-- proof
  apply StatMech.Sharpness.pBeta_lt_one J β

/--
[pBeta_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean)
-/
@[path]
private lemma pBeta_nonneg_eq
  {d : ℕ}
  {J β : ℝ}
-- given
  (h : 0 ≤ β * J) :
-- imply
  0 ≤ pBeta J β := by
-- proof
  apply StatMech.Sharpness.pBeta_nonneg h

/--
[pBeta_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean)
-/
@[path]
private lemma pBeta_strictMono_eq
  {d : ℕ}
  {J : ℝ}
-- given
  (hJ : 0 < J) :
-- imply
  StrictMono (pBeta J) := by
-- proof
  apply StatMech.Sharpness.pBeta_strictMono hJ

/--
[pBeta_toNNReal_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean)
-/
@[path]
private lemma pBeta_toNNReal_le_one_eq
  {d : ℕ}
  {J β : ℝ} :
-- imply
  (pBeta J β).toNNReal ≤ 1 := by
-- proof
  apply StatMech.Sharpness.pBeta_toNNReal_le_one J β

/--
[pBeta_betaTildeC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean)
-/
@[path]
private lemma pBeta_betaTildeC_eq
  {d : ℕ}
  {J : ℝ}
-- given
  (hJ : 0 < J)
  (htc1 : (tildePc d : ℝ) < 1) :
-- imply
  pBeta J (betaTildeC d J) = (tildePc d : ℝ) := by
-- proof
  apply StatMech.Sharpness.pBeta_betaTildeC hJ htc1

/--
[betaTildeC_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean)
-/
@[path]
private lemma betaTildeC_pos_eq
  {d : ℕ}
  {J : ℝ}
-- given
  (hJ : 0 < J)
  (hd : 0 < d)
  (htc1 : (tildePc d : ℝ) < 1) :
-- imply
  0 < betaTildeC d J := by
-- proof
  apply StatMech.Sharpness.betaTildeC_pos hJ hd htc1

/--
[one_sub_exp_secant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean)
-/
@[path]
private lemma one_sub_exp_secant_eq
  {d : ℕ}
  {J a b : ℝ}
-- given
  (ha : 0 < a)
  (hab : a ≤ b) :
-- imply
  a * (1 - Real.exp (-b * J)) ≤ b * (1 - Real.exp (-a * J)) := by
-- proof
  apply StatMech.Sharpness.one_sub_exp_secant J a b ha hab

/--
[pform_le_betaform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean)
-/
@[path]
private lemma pform_le_betaform_eq
  {d : ℕ}
  {J β βtc ptc thetaVal : ℝ}
-- given
  (hJ : 0 < J)
  (hβtc : 0 < βtc)
  (hβ : βtc < β)
  (hptc0 : 0 < ptc)
  (hptc1 : ptc < 1)
  (hptc_eq : ptc = 1 - Real.exp (-βtc * J))
  (hpform : ((1 - Real.exp (-β * J)) - ptc) / ((1 - Real.exp (-β * J)) * (1 - ptc)) ≤ thetaVal) :
-- imply
  (β - βtc) / β ≤ thetaVal := by
-- proof
  apply StatMech.Sharpness.pform_le_betaform J β βtc ptc thetaVal hJ hβtc hβ hptc0 hptc1 hptc_eq hpform

/--
[theta_ge_betaForm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/SharpnessBeta.lean)
-/
@[path]
private lemma theta_ge_betaForm_eq
  {d : ℕ}
  {J β : ℝ}
-- given
  (hJ : 0 < J)
  (hd : 0 < d)
  (htc1 : (tildePc d : ℝ) < 1)
  (hβ : betaTildeC d J < β) :
-- imply
  theta d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) ≥ (β - betaTildeC d J) / β := by
-- proof
  apply StatMech.Sharpness.theta_ge_betaForm hJ hd htc1 hβ


-- created on 2026-10-23
