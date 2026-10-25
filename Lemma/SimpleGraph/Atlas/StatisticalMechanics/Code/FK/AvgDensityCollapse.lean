import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.AvgDensityCollapse
open MeasureTheory Set Filter Topology Real StatMech StatMech.FK


/--
[adc_absavg_estimate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_absavg_estimate_eq
  [DecidableEq ι]
  {E I : Finset ι}
  {f : ι → ℝ}
  {L δ : ℝ}
-- given
  (hIE : I ⊆ E)
  (hf0 : ∀ e ∈ E, 0 ≤ f e)
  (hf1 : ∀ e ∈ E, f e ≤ 1)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hδ : 0 ≤ δ)
  (hin : ∀ e ∈ I, |f e - L| ≤ δ)
  (hE : 0 < E.card) :
-- imply
  |(1 / (E.card : ℝ)) * (∑ e ∈ E, f e) - L| ≤ δ + ((E.card - I.card : ℝ) / E.card) := by
-- proof
  apply StatMech.FK.adc_absavg_estimate E I hIE f L δ hf0 hf1 hL0 hL1 hδ hin hE

/--
[adc_absavg_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_absavg_tendsto_eq
  {ι : ℕ → Type*}
  [∀ n, DecidableEq (ι n)]
  {En In : (n : ℕ) → Finset (ι n)}
  {fn : (n : ℕ) → ι n → ℝ}
  {L : ℝ}
  {δ : ℕ → ℝ}
-- given
  (hIE : ∀ n, In n ⊆ En n)
  (hf0 : ∀ n, ∀ e ∈ En n, 0 ≤ fn n e)
  (hf1 : ∀ n, ∀ e ∈ En n, fn n e ≤ 1)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (hin : ∀ n, ∀ e ∈ In n, |fn n e - L| ≤ δ n)
  (hE : ∀ n, 0 < (En n).card)
  (hbdy : Tendsto (fun n => (((En n).card - (In n).card : ℝ)) / (En n).card) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => (1 / ((En n).card : ℝ)) * (∑ e ∈ En n, fn n e)) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.adc_absavg_tendsto En In fn L δ hIE hf0 hf1 hL0 hL1 hδ0 hδlim hin hE hbdy

/--
[adc_openCount_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_openCount_eq_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {ω : ConfigSpace (Sym2 V)} :
-- imply
  (openCount G ω : ℝ) = dfi_openEdgeCount G.edgeFinset ω := by
-- proof
  apply StatMech.FK.adc_openCount_eq_sum G ω

/--
[adc_fkExpect_openCount_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_fkExpect_openCount_eq_sum_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p : ℝ} :
-- imply
  fkExpect G p 2 (fun ω => (openCount G ω : ℝ)) = ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G p 2) e := by
-- proof
  apply StatMech.FK.adc_fkExpect_openCount_eq_sum G p

/--
[adc_avgDensity_eq_sum_edgeMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_avgDensity_eq_sum_edgeMarg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {t : ℝ} :
-- imply
  fpd_avgDensity G t = (1 / (G.edgeFinset.card : ℝ)) * ∑ e ∈ G.edgeFinset, edgeMargProb (fkProb G (fsc_logistic t) 2) e := by
-- proof
  apply StatMech.FK.adc_avgDensity_eq_sum_edgeMarg G t

/--
[adc_edgeMargProb_fkProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_edgeMargProb_fkProb_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  0 ≤ edgeMargProb (fkProb G p q) e := by
-- proof
  apply StatMech.FK.adc_edgeMargProb_fkProb_nonneg G hp hp1 hq e

/--
[adc_edgeMargProb_fkProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_edgeMargProb_fkProb_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  edgeMargProb (fkProb G p q) e ≤ 1 := by
-- proof
  apply StatMech.FK.adc_edgeMargProb_fkProb_le_one G hp hp1 hq e

/--
[adc_edgeMargProb_fkProb_mem_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_edgeMargProb_fkProb_mem_Icc_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {p q : ℝ}
  {e : Sym2 V}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q) :
-- imply
  edgeMargProb (fkProb G p q) e ∈ Set.Icc (0:ℝ) 1 := by
-- proof
  apply StatMech.FK.adc_edgeMargProb_fkProb_mem_Icc G hp hp1 hq e

/--
[adc_avgDensity_tendsto_of_homogeneity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_avgDensity_tendsto_of_homogeneity_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : ℕ}
  {t : ℝ}
  {L : ℝ}
  {In : (n : ℕ) → Finset (Sym2 (boxVerts d n))}
  {δ : ℕ → ℝ}
-- given
  (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hL0 : 0 ≤ L)
  (hL1 : L ≤ 1)
  (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
  (hδ0 : ∀ n, 0 ≤ δ n)
  (hδlim : Tendsto δ atTop (𝓝 0))
  (hin : ∀ n, ∀ e ∈ In n, |edgeMargProb (fkProb (boxGraph d n) (fsc_logistic t) 2) e - L| ≤ δ n)
  (hbdy : Tendsto (fun n => (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card) atTop (𝓝 0)) :
-- imply
  Tendsto (fun n => fpd_avgDensity (boxGraph d n) t) atTop (𝓝 L) := by
-- proof
  apply StatMech.FK.adc_avgDensity_tendsto_of_homogeneity G d t hE L hL0 hL1 In hIE δ hδ0 hδlim hin hbdy

/--
[adc_residues_remark](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/AvgDensityCollapse.lean)
-/
@[path]
private lemma adc_residues_remark_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  True := by
-- proof
  apply StatMech.FK.adc_residues_remark G


-- created on 2026-10-23
