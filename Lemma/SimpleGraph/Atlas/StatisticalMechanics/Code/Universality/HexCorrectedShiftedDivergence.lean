import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexCorrectedShiftedDivergence
open StatMech StatMech.Universality StatMech.Universality.HexAsymmetricHighestCut


/--
[recursion_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedShiftedDivergence.lean)
-/
@[path]
private lemma recursion_bound_eq
  {K : ℝ}
  {H : HexAsymmetricHighestCut K}
-- given
  (hK : 0 ≤ K) :
-- imply
  (∑' d, H.wtγ d) ≤ K * ((∑' b, H.wtB₁ b) * (∑' b, H.wtB₂ b)) := by
-- proof
  apply StatMech.Universality.HexAsymmetricHighestCut.recursion_bound H hK

/--
[hex_shifted_reciprocal_not_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedShiftedDivergence.lean)
-/
@[path]
private lemma hex_shifted_reciprocal_not_summable_eq
  {K : ℝ}
  {shift₁ shift₂ : ℕ}
  {lam ups : ℕ → ℝ}
-- given
  (hK : 0 < K)
  (hshift₁ : 1 ≤ shift₁)
  (hshift₂ : 1 ≤ shift₂)
  (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + ups v = 1)
  (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
  (hupsnn : ∀ v, 0 ≤ ups v)
  (hupsOne : 0 < ups 1)
  (hrec : ∀ v, 1 ≤ v → lam (v + 1) - lam v ≤ K * (ups (v + shift₁) * ups (v + shift₂))) :
-- imply
  ¬ Summable ups := by
-- proof
  apply StatMech.Universality.hex_shifted_reciprocal_not_summable K hK shift₁ shift₂ hshift₁ hshift₂ lam ups hbdry hlamMono hupsnn hupsOne hrec

/--
[hexCS_critical_divergence_of_shifted_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCorrectedShiftedDivergence.lean)
-/
@[path]
private lemma hexCS_critical_divergence_of_shifted_recurrence_eq
  {K : ℝ}
  {shift₁ shift₂ : ℕ}
-- given
  (hK : 0 < K)
  (hshift₁ : 1 ≤ shift₁)
  (hshift₂ : 1 ≤ shift₂)
  (hlocal : ∀ T L (hT : 0 < T), HexCSLocalRelation T L hT)
  (hwindow : ∀ T L (hT : 0 < T), HexCSBoundaryWindowLaw T L hT)
  (hrec : Summable (hexEndpointSAWwt hexAWStart 1 hexChiE) → ∀ T, 1 ≤ T → hexCSInfiniteSideMassAtWidth (T + 1) - hexCSInfiniteSideMassAtWidth T ≤ K * (hexCSInfiniteTopMassAtWidth (T + shift₁) * hexCSInfiniteTopMassAtWidth (T + shift₂)))
  (htopOne : ∃ ts, HexCSTopWalkAtWidth 1 (by norm_num) ts) :
-- imply
  ¬ Summable (fun n : ℕ => hlc_sawCountR hexAWStart 1 n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexCS_critical_divergence_of_shifted_recurrence K hK shift₁ shift₂ hshift₁ hshift₂ hlocal hwindow hrec htopOne


-- created on 2026-10-23
