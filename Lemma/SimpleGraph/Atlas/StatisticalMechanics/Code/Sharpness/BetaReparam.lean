import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BetaReparam
open MeasureTheory Set Filter Topology Real StatMech StatMech.Sharpness


/--
[shr_pBeta_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaReparam.lean)
-/
@[path]
private lemma shr_pBeta_hasDerivAt_eq
  {d : ℕ}
  {J β : ℝ} :
-- imply
  HasDerivAt (pBeta J) (J * Real.exp (-β * J)) β := by
-- proof
  apply StatMech.Sharpness.shr_pBeta_hasDerivAt J β

/--
[shr_pBeta_le_betaJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaReparam.lean)
-/
@[path]
private lemma shr_pBeta_le_betaJ_eq
  {d : ℕ}
  {J β : ℝ} :
-- imply
  pBeta J β ≤ β * J := by
-- proof
  apply StatMech.Sharpness.shr_pBeta_le_betaJ J β

/--
[shr_meanfield_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaReparam.lean)
-/
@[path]
private lemma shr_meanfield_beta_eq
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
  apply StatMech.Sharpness.shr_meanfield_beta J β m fp' f hJ hβ hp0 hp1 hm hf1 hf hpform

/--
[shr_meanfield_beta_crossProbReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaReparam.lean)
-/
@[path]
private lemma shr_meanfield_beta_crossProbReal_eq
  {d : ℕ}
  {q : NNReal}
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
  apply StatMech.Sharpness.shr_meanfield_beta_crossProbReal J β hJ hβ hq1 htpc0 n ht

/--
[shr_integrate_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaReparam.lean)
-/
@[path]
private lemma shr_integrate_beta_eq
  {d : ℕ}
  {J β β₀ : ℝ}
  {f : ℝ → ℝ}
-- given
  (hJ : 0 < J)
  (hβ₀ : 0 < β₀)
  (hββ₀ : β₀ < β)
  (hdiff : ∀ q ∈ Ico (pBeta J β₀) 1, DifferentiableAt ℝ f q)
  (hineq : ∀ q ∈ Ioo (pBeta J β₀) 1, (1 / (q * (1 - q))) * (1 - f q) ≤ deriv f q)
  (hf0 : 0 ≤ f (pBeta J β₀)) :
-- imply
  (β - β₀) / β ≤ f (pBeta J β) := by
-- proof
  apply StatMech.Sharpness.shr_integrate_beta J β β₀ f hJ hβ₀ hββ₀ hdiff hineq hf0

/--
[shr_item3_beta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BetaReparam.lean)
-/
@[path]
private lemma shr_item3_beta_eq
  {d : ℕ}
  {J β : ℝ}
  {S : Finset (Site d)}
  {L : ℕ}
-- given
  (hoS : origin d ∈ (S : Set (Site d)))
  (hphi : phi d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) S < 1)
  (hL : 1 ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - 1)) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, crossProb d (pBeta J β).toNNReal (pBeta_toNNReal_le_one J β) n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Sharpness.shr_item3_beta J β S hoS hphi L hL hSbox


-- created on 2026-10-23
