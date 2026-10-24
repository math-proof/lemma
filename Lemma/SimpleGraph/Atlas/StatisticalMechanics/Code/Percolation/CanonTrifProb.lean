import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.CanonTrifProb
open StatMech StatMech.Percolation


/--
[ctp_measurableSet_openAdj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonTrifProb.lean)
-/
@[path]
private lemma ctp_measurableSet_openAdj_eq
  {d : ℕ}
  {x a : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (openSubgraph d ω).Adj x a} := by
-- proof
  apply StatMech.Percolation.ctp_measurableSet_openAdj x a

/--
[ctp_measurableSet_removeSiteClusterInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonTrifProb.lean)
-/
@[path]
private lemma ctp_measurableSet_removeSiteClusterInfinite_eq
  {d : ℕ}
  {x a : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | (cluster d (removeSite x ω) a).Infinite} := by
-- proof
  apply StatMech.Percolation.ctp_measurableSet_removeSiteClusterInfinite x a

/--
[ctp_measurableSet_isCanonicalTrifurcation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonTrifProb.lean)
-/
@[path]
private lemma ctp_measurableSet_isCanonicalTrifurcation_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  MeasurableSet {ω : ConfigSpace (Sym2 (Site d)) | IsCanonicalTrifurcation d ω x} := by
-- proof
  apply StatMech.Percolation.ctp_measurableSet_isCanonicalTrifurcation x

/--
[ctp_isCanonicalTrifurcation_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonTrifProb.lean)
-/
@[path]
private lemma ctp_isCanonicalTrifurcation_shift_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  IsCanonicalTrifurcation d (shift g ω) (g • x) ↔ IsCanonicalTrifurcation d ω x := by
-- proof
  apply StatMech.Percolation.ctp_isCanonicalTrifurcation_shift g ω x

/--
[ctp_canonicalTrifurcationProb_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonTrifProb.lean)
-/
@[path]
private lemma ctp_canonicalTrifurcationProb_const_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {x : Site d}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  μ {ω | IsCanonicalTrifurcation d ω x} = μ {ω | IsCanonicalTrifurcation d ω 0} := by
-- proof
  apply StatMech.Percolation.ctp_canonicalTrifurcationProb_const μ hinv x

/--
[ctp_canonTcount_eq_sum_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonTrifProb.lean)
-/
@[path]
private lemma ctp_canonTcount_eq_sum_indicator_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {n : ℕ} :
-- imply
  (ctc2_canonTcount d ω n : ℝ≥0∞) = ∑ x ∈ boxFinsetBK d n, ({ω' | IsCanonicalTrifurcation d ω' x}.indicator (fun _ => (1 : ℝ≥0∞))) ω := by
-- proof
  apply StatMech.Percolation.ctp_canonTcount_eq_sum_indicator ω n

/--
[ctp_expected_canonTcount](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonTrifProb.lean)
-/
@[path]
private lemma ctp_expected_canonTcount_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  {n : ℕ}
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ) :
-- imply
  ∫⁻ ω, (ctc2_canonTcount d ω n : ℝ≥0∞) ∂μ = (boxFinsetBK d n).card • μ {ω | IsCanonicalTrifurcation d ω 0} := by
-- proof
  apply StatMech.Percolation.ctp_expected_canonTcount μ hinv n

/--
[ctp_canonical_trifurcation_prob_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/CanonTrifProb.lean)
-/
@[path]
private lemma ctp_canonical_trifurcation_prob_eq_zero_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Sym2 (Site d)))}
  [IsProbabilityMeasure μ]
-- given
  (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
  (hvol : ∀ n, 0 < (boxFinsetBK d n).card)
  (hdens : Filter.Tendsto (fun n => (boxSV_boundaryCard d (n + 1) : ℝ) / ((boxFinsetBK d n).card : ℝ)) Filter.atTop (nhds 0)) :
-- imply
  μ {ω | IsCanonicalTrifurcation d ω 0} = 0 := by
-- proof
  apply StatMech.Percolation.ctp_canonical_trifurcation_prob_eq_zero μ hinv hvol hdens


-- created on 2026-10-23
