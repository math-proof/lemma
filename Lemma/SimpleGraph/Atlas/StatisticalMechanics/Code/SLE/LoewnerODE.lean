import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.SLE.LoewnerODE
open Complex Set Metric Filter Topology StatMech StatMech.SLE


/--
[mem_loewnerStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma mem_loewnerStrip_eq
  {δ : ℝ}
  {w : ℂ} :
-- imply
  w ∈ loewnerStrip δ ↔ δ ≤ w.im := by
-- proof
  apply StatMech.SLE.mem_loewnerStrip

/--
[loewnerStrip_subset_upperHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma loewnerStrip_subset_upperHalfPlane_eq
  {δ : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  loewnerStrip δ ⊆ upperHalfPlane := by
-- proof
  apply StatMech.SLE.loewnerStrip_subset_upperHalfPlane hδ

/--
[isClosed_loewnerStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma isClosed_loewnerStrip_eq
  {δ : ℝ} :
-- imply
  IsClosed (loewnerStrip δ) := by
-- proof
  apply StatMech.SLE.isClosed_loewnerStrip δ

/--
[le_norm_sub_ofReal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma le_norm_sub_ofReal_eq
  {δ : ℝ}
  {x : ℝ}
  {w : ℂ}
-- given
  (hw : δ ≤ w.im) :
-- imply
  δ ≤ ‖w - (x : ℂ)‖ := by
-- proof
  apply StatMech.SLE.le_norm_sub_ofReal hw

/--
[loewnerField_lipschitzOnWith](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma loewnerField_lipschitzOnWith_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {t : ℝ}
-- given
  (hδ : 0 < δ) :
-- imply
  LipschitzOnWith ((2 / δ ^ 2).toNNReal) (loewnerField W t) (loewnerStrip δ) := by
-- proof
  apply StatMech.SLE.loewnerField_lipschitzOnWith W hδ t

/--
[loewnerField_norm_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma loewnerField_norm_le_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {t : ℝ}
  {w : ℂ}
-- given
  (hδ : 0 < δ)
  (hw : w ∈ loewnerStrip δ) :
-- imply
  ‖loewnerField W t w‖ ≤ 2 / δ := by
-- proof
  apply StatMech.SLE.loewnerField_norm_le W hδ t hw

/--
[continuousOn_loewnerField_time](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma continuousOn_loewnerField_time_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {w : ℂ}
  {s : Set ℝ}
-- given
  (hW : Continuous W)
  (hδ : 0 < δ)
  (hw : w ∈ loewnerStrip δ) :
-- imply
  ContinuousOn (fun t => loewnerField W t w) s := by
-- proof
  apply StatMech.SLE.continuousOn_loewnerField_time hW hδ hw s

/--
[closedBall_subset_loewnerStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma closedBall_subset_loewnerStrip_eq
  {z₀ : ℂ}
  {a δ : ℝ}
-- given
  (h : δ ≤ z₀.im - a) :
-- imply
  closedBall z₀ a ⊆ loewnerStrip δ := by
-- proof
  apply StatMech.SLE.closedBall_subset_loewnerStrip h

/--
[isPicardLindelof_loewnerField](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma isPicardLindelof_loewnerField_eq
  {W : ℝ → ℝ}
  {z₀ : ℂ}
  {t₀ : ℝ}
-- given
  (hW : Continuous W)
  (hz₀ : 0 < z₀.im) :
-- imply
  IsPicardLindelof (loewnerField W) (tmin := t₀ - (z₀.im ^ 2 / 8)) (tmax := t₀ + (z₀.im ^ 2 / 8)) ⟨t₀, by constructor <;> nlinarith [hz₀]⟩ z₀ (z₀.im / 2).toNNReal 0 (2 / (z₀.im / 2)).toNNReal ((2 / (z₀.im / 2) ^ 2).toNNReal) := by
-- proof
  apply StatMech.SLE.isPicardLindelof_loewnerField hW hz₀ t₀

/--
[isPicardLindelof_loewnerField_neighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma isPicardLindelof_loewnerField_neighborhood_eq
  {W : ℝ → ℝ}
  {z₀ : ℂ}
  {t₀ : ℝ}
-- given
  (hW : Continuous W)
  (hz₀ : 0 < z₀.im) :
-- imply
  IsPicardLindelof (loewnerField W) (tmin := t₀ - (z₀.im ^ 2 / 16)) (tmax := t₀ + (z₀.im ^ 2 / 16)) ⟨t₀, by constructor <;> nlinarith [sq_pos_of_pos hz₀]⟩ z₀ (z₀.im / 2).toNNReal (z₀.im / 4).toNNReal (2 / (z₀.im / 2)).toNNReal ((2 / (z₀.im / 2) ^ 2).toNNReal) := by
-- proof
  apply StatMech.SLE.isPicardLindelof_loewnerField_neighborhood hW hz₀ t₀

/--
[exists_isLoewnerSolutionOn_Icc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma exists_isLoewnerSolutionOn_Icc_eq
  {W : ℝ → ℝ}
  {z₀ : ℂ}
  {t₀ : ℝ}
-- given
  (hW : Continuous W)
  (hz₀ : 0 < z₀.im) :
-- imply
  ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g t₀ = z₀ ∧ ∀ t ∈ Icc (t₀ - ε) (t₀ + ε), HasDerivWithinAt g (loewnerField W t (g t)) (Icc (t₀ - ε) (t₀ + ε)) t := by
-- proof
  apply StatMech.SLE.exists_isLoewnerSolutionOn_Icc hW hz₀ t₀

/--
[exists_isLoewnerSolution_hasDerivAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma exists_isLoewnerSolution_hasDerivAt_eq
  {W : ℝ → ℝ}
  {z₀ : ℂ}
  {t₀ : ℝ}
-- given
  (hW : Continuous W)
  (hz₀ : 0 < z₀.im) :
-- imply
  ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, g t₀ = z₀ ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt g (loewnerField W t (g t)) t := by
-- proof
  apply StatMech.SLE.exists_isLoewnerSolution_hasDerivAt hW hz₀ t₀

/--
[exists_isLoewnerSolutionOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma exists_isLoewnerSolutionOn_eq
  {W : ℝ → ℝ}
  {z₀ : ℂ}
  {t₀ : ℝ}
-- given
  (hW : Continuous W)
  (hz₀ : 0 < z₀.im) :
-- imply
  ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ → ℂ, g t₀ z₀ = z₀ ∧ IsLoewnerSolutionOn W g z₀ (Icc (t₀ - ε) (t₀ + ε)) := by
-- proof
  apply StatMech.SLE.exists_isLoewnerSolutionOn hW hz₀ t₀

/--
[loewnerSolution_unique_Ioo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma loewnerSolution_unique_Ioo_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {a b t₀ : ℝ}
  {g h : ℝ → ℂ}
-- given
  (hδ : 0 < δ)
  (ht₀ : t₀ ∈ Ioo a b)
  (hg : ∀ t ∈ Ioo a b, HasDerivAt g (loewnerField W t (g t)) t ∧ g t ∈ loewnerStrip δ)
  (hh : ∀ t ∈ Ioo a b, HasDerivAt h (loewnerField W t (h t)) t ∧ h t ∈ loewnerStrip δ)
  (heq : g t₀ = h t₀) :
-- imply
  EqOn g h (Ioo a b) := by
-- proof
  apply StatMech.SLE.loewnerSolution_unique_Ioo hδ ht₀ hg hh heq

/--
[loewnerSolution_unique_Icc_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma loewnerSolution_unique_Icc_right_eq
  {W : ℝ → ℝ}
  {δ : ℝ}
  {a b : ℝ}
  {g h : ℝ → ℂ}
-- given
  (hδ : 0 < δ)
  (hg : ContinuousOn g (Icc a b))
  (hg' : ∀ t ∈ Ico a b, HasDerivWithinAt g (loewnerField W t (g t)) (Ici t) t)
  (hgs : ∀ t ∈ Ico a b, g t ∈ loewnerStrip δ)
  (hh : ContinuousOn h (Icc a b))
  (hh' : ∀ t ∈ Ico a b, HasDerivWithinAt h (loewnerField W t (h t)) (Ici t) t)
  (hhs : ∀ t ∈ Ico a b, h t ∈ loewnerStrip δ)
  (heq : g a = h a) :
-- imply
  EqOn g h (Icc a b) := by
-- proof
  apply StatMech.SLE.loewnerSolution_unique_Icc_right hδ hg hg' hgs hh hh' hhs heq

/--
[exists_unique_loewnerSolution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/SLE/LoewnerODE.lean)
-/
@[path]
private lemma exists_unique_loewnerSolution_eq
  {W : ℝ → ℝ}
  {z₀ : ℂ}
  {t₀ : ℝ}
-- given
  (hW : Continuous W)
  (hz₀ : 0 < z₀.im) :
-- imply
  ∃ ε > (0 : ℝ), ∃ g : ℝ → ℂ, (g t₀ = z₀ ∧ ∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt g (loewnerField W t (g t)) t) ∧ ∀ h : ℝ → ℂ, h t₀ = z₀ → (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), HasDerivAt h (loewnerField W t (h t)) t ∧ h t ∈ loewnerStrip (z₀.im / 2)) → (∀ t ∈ Ioo (t₀ - ε) (t₀ + ε), g t ∈ loewnerStrip (z₀.im / 2)) → EqOn g h (Ioo (t₀ - ε) (t₀ + ε)) := by
-- proof
  apply StatMech.SLE.exists_unique_loewnerSolution hW hz₀ t₀


-- created on 2026-10-23
