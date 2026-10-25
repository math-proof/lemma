import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.LogCesaroLimit.Part2
open Filter Topology Real Finset StatMech StatMech.OSSS StatMech.OSSS.LogCesaroLimit


/--
[harmonicReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma harmonicReal_eq_eq
  {n : ℕ} :
-- imply
  harmonicReal n = (harmonic n : ℝ) := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.harmonicReal_eq n

/--
[harmonicReal_div_log_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma harmonicReal_div_log_tendsto_one_eq :
-- imply
  Tendsto (fun n => harmonicReal n / Real.log (n : ℝ)) atTop (nhds 1) := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.harmonicReal_div_log_tendsto_one

/--
[logCesaro_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma logCesaro_tendsto_eq
  {u : ℕ → ℝ}
  {l : ℝ}
-- given
  (hu : Tendsto u atTop (nhds l)) :
-- imply
  Tendsto (fun n => logCesaro u n) atTop (nhds l) := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.logCesaro_tendsto hu

/--
[meanLogTerm_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma meanLogTerm_tendsto_eq
  {fseq : ℕ → ℝ → ℝ}
  {x l : ℝ}
-- given
  (h : Tendsto (fun n => fseq n x) atTop (nhds l)) :
-- imply
  Tendsto (fun n => Integration.meanLogTerm fseq n x) atTop (nhds l) := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.meanLogTerm_tendsto h

/--
[logRatio_partialSum_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma logRatio_partialSum_tendsto_one_eq
  {u : ℕ → ℝ}
  {l : ℝ}
-- given
  (hu : Tendsto u atTop (nhds l))
  (hl : 0 < l) :
-- imply
  Tendsto (BetaThresholdBound.logRatio (fun n => ∑ k ∈ Finset.range n, u k)) atTop (nhds 1) := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.logRatio_partialSum_tendsto_one hu hl

/--
[wiredBox_logCesaro_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma wiredBox_logCesaro_tendsto_eq
  {d : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun n => logCesaro (fun k => IsingFK.boxBoundaryConnProfile d hp hp1 (by norm_num : (0 : ℝ) < 2) k) n) atTop (nhds (FK.fkTheta d hp hp1 (by norm_num : (0 : ℝ) < 2) (q := 2))) := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.wiredBox_logCesaro_tendsto hp hp1

/--
[thresholdSet_upward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma thresholdSet_upward_eq
  {Sgf : ℝ → ℕ → ℝ}
  {a b : ℝ}
-- given
  (hmono : ∀ {a b : ℝ}, a ≤ b → ∀ n, Sgf a n ≤ Sgf b n)
  (hpos : ∀ b n, 2 ≤ n → 0 < Sgf b n)
  (hcob : ∀ b, IsCoboundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
  (hbdd : ∀ b, IsBoundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
  (hab : a ≤ b)
  (ha : a ∈ thresholdSet Sgf) :
-- imply
  b ∈ thresholdSet Sgf := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.thresholdSet_upward hmono hpos hcob hbdd hab ha

/--
[one_le_limsup_of_beta1_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma one_le_limsup_of_beta1_lt_eq
  {Sgf : ℝ → ℕ → ℝ}
  {b : ℝ}
-- given
  (hne : (thresholdSet Sgf).Nonempty)
  (hmono : ∀ {a b : ℝ}, a ≤ b → ∀ n, Sgf a n ≤ Sgf b n)
  (hpos : ∀ b n, 2 ≤ n → 0 < Sgf b n)
  (hcob : ∀ b, IsCoboundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
  (hbdd : ∀ b, IsBoundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
  (hb : beta1 Sgf < b) :
-- imply
  1 ≤ limsup (logRatio (Sgf b)) atTop := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.one_le_limsup_of_beta1_lt hne hmono hpos hcob hbdd hb

/--
[thresholdRate_limit_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma thresholdRate_limit_data_eq
  {Sgf : ℝ → ℕ → ℝ}
  {b : ℝ}
-- given
  (hne : (thresholdSet Sgf).Nonempty)
  (hmono : ∀ {a b : ℝ}, a ≤ b → ∀ n, Sgf a n ≤ Sgf b n)
  (hpos : ∀ b n, 2 ≤ n → 0 < Sgf b n)
  (hcob : ∀ b, IsCoboundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
  (hbdd : ∀ b, IsBoundedUnder (· ≤ ·) atTop (logRatio (Sgf b)))
  (hb : beta1 Sgf < b) :
-- imply
  ∃ (mseq : ℕ → ℝ) (m : ℝ), Tendsto mseq atTop (nhds m) ∧ 1 ≤ m := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.thresholdRate_limit_data hne hmono hpos hcob hbdd hb

/--
[meanField_lower_of_limsup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma meanField_lower_of_limsup_eq
  {T : ℕ → ℝ → ℝ}
  {rate error : ℕ → ℝ}
  {β' β fβ fβ' : ℝ}
-- given
  (hββ : β' ≤ β)
  (hTβ : Tendsto (fun n => T n β) atTop (nhds fβ))
  (hTβ' : Tendsto (fun n => T n β') atTop (nhds fβ'))
  (herror : Tendsto error atTop (nhds 0))
  (hcob : IsCoboundedUnder (· ≤ ·) atTop rate)
  (hbdd : IsBoundedUnder (· ≤ ·) atTop rate)
  (hm1 : 1 ≤ limsup rate atTop)
  (hbound : ∀ᶠ n in atTop, (β - β') * (rate n + error n) ≤ T n β - T n β') :
-- imply
  β - β' ≤ fβ - fβ' := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.meanField_lower_of_limsup hββ hTβ hTβ' herror hcob hbdd hm1 hbound

/--
[meanField_lower_of_threshold_rate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma meanField_lower_of_threshold_rate_eq
  {fseq fpseq : ℕ → ℝ → ℝ}
  {Sig : ℕ → ℝ → ℝ}
  {β' β fβ fβ' C : ℝ}
-- given
  (hββ : β' ≤ β)
  (hf : ∀ i x, x ∈ Set.Icc β' β → HasDerivAt (fun x => fseq i x) (fpseq i x) x)
  (hSrec : ∀ i x, Sig (i + 1) x = Sig i x + fseq i x)
  (hfnn : ∀ i x, 1 ≤ i → x ∈ Set.Icc β' β → 0 ≤ fseq i x)
  (hSpos : ∀ i x, 1 ≤ i → x ∈ Set.Icc β' β → 0 < Sig i x)
  (hdiff : ∀ i : ℕ, ∀ x, 1 ≤ i → x ∈ Set.Icc β' β → ((i : ℝ) / Sig i x) * fseq i x ≤ fpseq i x)
  (hSmono : ∀ n x, 1 ≤ n → x ∈ Set.Icc β' β → Sig n β' ≤ Sig (n + 1) x)
  (hS1le : ∀ x ∈ Set.Icc β' β, Sig 1 x ≤ C)
  (hTβ : Tendsto (fun n => Integration.meanLogTerm fseq n β) atTop (nhds fβ))
  (hTβ' : Tendsto (fun n => Integration.meanLogTerm fseq n β') atTop (nhds fβ'))
  (hcob : IsCoboundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig n β')))
  (hbdd : IsBoundedUnder (· ≤ ·) atTop (logRatio (fun n => Sig n β')))
  (hm1 : 1 ≤ limsup (logRatio (fun n => Sig n β')) atTop) :
-- imply
  β - β' ≤ fβ - fβ' := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.meanField_lower_of_threshold_rate fseq fpseq Sig β' β fβ fβ' C hββ hf hSrec hfnn hSpos hdiff hSmono hS1le hTβ hTβ' hcob hbdd hm1

/--
[meanField_lower_at_threshold](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/LogCesaroLimit.lean)
-/
@[path]
private lemma meanField_lower_at_threshold_eq
  {f : ℝ → ℝ}
  {β₁ β : ℝ}
-- given
  (hβ : β₁ < β)
  (hfnn : ∀ β', β₁ < β' → β' < β → 0 ≤ f β')
  (hinterior : ∀ β', β₁ < β' → β' < β → β - β' ≤ f β - f β') :
-- imply
  β - β₁ ≤ f β := by
-- proof
  apply StatMech.OSSS.LogCesaroLimit.meanField_lower_at_threshold hβ hfnn hinterior


-- created on 2026-10-23
