import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BetaFormPerco
open MeasureTheory Set Filter Topology Real StatMech StatMech.Sharpness


/--
[bfp_pBeta_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaFormPerco.lean)
-/
@[path]
private lemma bfp_pBeta_hasDerivAt_eq
  {d : ℕ}
  {J β : ℝ} :
-- imply
  HasDerivAt (pBeta J) (J * Real.exp (-β * J)) β := by
-- proof
  apply StatMech.Sharpness.bfp_pBeta_hasDerivAt J β

/--
[bfp_pBeta_le_betaJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaFormPerco.lean)
-/
@[path]
private lemma bfp_pBeta_le_betaJ_eq
  {d : ℕ}
  {J β : ℝ} :
-- imply
  pBeta J β ≤ β * J := by
-- proof
  apply StatMech.Sharpness.bfp_pBeta_le_betaJ J β

/--
[bfp_meanfield_perco_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaFormPerco.lean)
-/
@[path]
private lemma bfp_meanfield_perco_beta_eq
  {d : ℕ}
  {J β m fp' : ℝ}
  {f : ℝ → ℝ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β)
  (hp0 : 0 < pBeta J β)
  (hp1 : pBeta J β < 1)
  (hm : 0 ≤ m)
  (hf1 : f (pBeta J β) ≤ 1)
  (hf : HasDerivAt f fp' (pBeta J β))
  (hpform : (1 / (pBeta J β * (1 - pBeta J β))) * m * (1 - f (pBeta J β)) ≤ fp') :
-- imply
  HasDerivAt (fun b => f (pBeta J b)) (fp' * (J * Real.exp (-β * J))) β ∧ (1 / β) * m * (1 - f (pBeta J β)) ≤ fp' * (J * Real.exp (-β * J)) := by
-- proof
  apply StatMech.Sharpness.bfp_meanfield_perco_beta J β m fp' f hJ hβ hp0 hp1 hm hf1 hf hpform

/--
[bfp_meanfield_perco_beta_crossProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaFormPerco.lean)
-/
@[path]
private lemma bfp_meanfield_perco_beta_crossProb_eq
  {d : ℕ}
  {q : ℝ≥0}
  {J β : ℝ}
  {n : ℕ}
-- given
  (hJ : 0 < J)
  (hβ : 0 < β)
  (hq1 : (q : ℝ) < 1)
  (htpc0 : 0 < (tildePc d : ℝ))
  (ht : pBeta J β ∈ Ioo (tildePc d : ℝ) (q : ℝ)) :
-- imply
  HasDerivAt (fun b => crossProbReal d (n + 1) (pBeta J b)) (deriv (crossPoly d n) (pBeta J β) * (J * Real.exp (-β * J))) β ∧ (1 / β) * (1 - crossProbReal d (n + 1) (pBeta J β)) ≤ deriv (crossPoly d n) (pBeta J β) * (J * Real.exp (-β * J)) := by
-- proof
  apply StatMech.Sharpness.bfp_meanfield_perco_beta_crossProb J β hJ hβ hq1 htpc0 n ht

/--
[bfp_integrate_perco_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaFormPerco.lean)
-/
@[path]
private lemma bfp_integrate_perco_beta_eq
  {d : ℕ}
  {J β βc : ℝ}
  {f : ℝ → ℝ}
-- given
  (hJ : 0 < J)
  (hβc : 0 < βc)
  (hββc : βc < β)
  (hdiff : ∀ q ∈ Ico (pBeta J βc) 1, DifferentiableAt ℝ f q)
  (hineq : ∀ q ∈ Ioo (pBeta J βc) 1, (1 / (q * (1 - q))) * (1 - f q) ≤ deriv f q)
  (hf0 : 0 ≤ f (pBeta J βc)) :
-- imply
  (β - βc) / β ≤ f (pBeta J β) := by
-- proof
  apply StatMech.Sharpness.bfp_integrate_perco_beta J β βc f hJ hβc hββc hdiff hineq hf0

/--
[bfp_integrate_perco_beta_named](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaFormPerco.lean)
-/
@[path]
private lemma bfp_integrate_perco_beta_named_eq
  {d : ℕ}
  {J β : ℝ}
  {f : ℝ → ℝ}
-- given
  (hJ : 0 < J)
  (hd : 0 < d)
  (htc1 : (tildePc d : ℝ) < 1)
  (hβ : betaTildeC d J < β)
  (hdiff : ∀ q ∈ Ico (tildePc d : ℝ) 1, DifferentiableAt ℝ f q)
  (hineq : ∀ q ∈ Ioo (tildePc d : ℝ) 1, (1 / (q * (1 - q))) * (1 - f q) ≤ deriv f q)
  (hf0 : 0 ≤ f (tildePc d : ℝ)) :
-- imply
  (β - betaTildeC d J) / β ≤ f (pBeta J β) := by
-- proof
  apply StatMech.Sharpness.bfp_integrate_perco_beta_named f hJ hd htc1 hβ hdiff hineq hf0


-- created on 2026-10-23
