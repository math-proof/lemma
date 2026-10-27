import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Foundations.KingmanFilling.Part2
open MeasureTheory Filter Topology StatMech StatMech.KingmanFilling


/--
[aemeasurable_gStarLow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma aemeasurable_gStarLow_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  AEMeasurable (gStarLow T X) μ := by
-- proof
  apply StatMech.KingmanFilling.aemeasurable_gStarLow h

/--
[aemeasurable_gLow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma aemeasurable_gLow_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  AEMeasurable (gLow T X) μ := by
-- proof
  apply StatMech.KingmanFilling.aemeasurable_gLow h

/--
[gStarLow_nonneg_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gStarLow_nonneg_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, (0 : EReal) ≤ gStarLow T X x := by
-- proof
  apply StatMech.KingmanFilling.gStarLow_nonneg_ae hnn

/--
[gLow_nonneg_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gLow_nonneg_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, 0 ≤ gLow T X x := by
-- proof
  apply StatMech.KingmanFilling.gLow_nonneg_ae hnn

/--
[eq_of_le_toReal_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma eq_of_le_toReal_eq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {x y : EReal}
-- given
  (hle : x ≤ y)
  (hxbot : x ≠ ⊥)
  (hytop : y ≠ ⊤)
  (heq : x.toReal = y.toReal) :
-- imply
  x = y := by
-- proof
  apply StatMech.KingmanFilling.eq_of_le_toReal_eq hle hxbot hytop heq

/--
[gStarLow_le_comp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gStarLow_le_comp_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∀ᵐ x ∂μ, gStarLow T X x ≤ gStarLow T X (T x) := by
-- proof
  apply StatMech.KingmanFilling.gStarLow_le_comp h

/--
[dep_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma dep_nonneg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {ε : ℝ}
  {N : ℕ}
  {y : α}
-- given
  (hg : 0 ≤ gLow T X y)
  (hε : 0 ≤ ε)
  (hx1 : 0 ≤ X 1 y) :
-- imply
  0 ≤ dep T X ε N y := by
-- proof
  apply StatMech.KingmanFilling.dep_nonneg hg hε hx1

/--
[greedy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma greedy_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {ε : ℝ}
  {N : ℕ}
  {x : α}
-- given
  (hN : 1 ≤ N)
  (hsub : ∀ s a b, X (a + b) (T^[s] x) ≤ X a (T^[s] x) + X b (T^[a + s] x))
  (hmono : ∀ i j, i ≤ j → gLow T X (T^[i] x) ≤ gLow T X (T^[j] x))
  (hgnn : ∀ i, 0 ≤ gLow T X (T^[i] x))
  (hx1nn : ∀ i, 0 ≤ X 1 (T^[i] x))
  (hεnn : 0 ≤ ε)
  (hrem : ∀ i n, n < N → X n (T^[i] x) ≤ remDom X N (T^[i] x)) :
-- imply
  ∀ n s, ∃ m, m ≤ n ∧ n ≤ m + N ∧ X n (T^[s] x) ≤ (∑ j ∈ Finset.range n, dep T X ε N (T^[s + j] x)) + remDom X N (T^[s + m] x) := by
-- proof
  apply StatMech.KingmanFilling.greedy ε N hN x hsub hmono hgnn hx1nn hεnn hrem

/--
[greedy_windowed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma greedy_windowed_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  {ε : ℝ}
  {N : ℕ}
  {x : α}
  {n : ℕ}
-- given
  (hN : 1 ≤ N)
  (hsub : ∀ s a b, X (a + b) (T^[s] x) ≤ X a (T^[s] x) + X b (T^[a + s] x))
  (hmono : ∀ i j, i ≤ j → gLow T X (T^[i] x) ≤ gLow T X (T^[j] x))
  (hgnn : ∀ i, 0 ≤ gLow T X (T^[i] x))
  (hx1nn : ∀ i, 0 ≤ X 1 (T^[i] x))
  (hεnn : 0 ≤ ε)
  (hremnn : ∀ t, 0 ≤ remDom X N (T^[t] x)) :
-- imply
  X n x ≤ (∑ j ∈ Finset.range n, dep T X ε N (T^[j] x)) + ∑ t ∈ Finset.Icc (n-N) n, remDom X N (T^[t] x) := by
-- proof
  apply StatMech.KingmanFilling.greedy_windowed ε N hN x hsub hmono hgnn hx1nn hεnn hremnn n

/--
[gLow_le_kingmanLimit_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gLow_le_kingmanLimit_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, gLow T X x ≤ kingmanLimit T X x := by
-- proof
  apply StatMech.KingmanFilling.gLow_le_kingmanLimit_ae h hnn

/--
[integrable_gLow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma integrable_gLow_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  Integrable (gLow T X) μ := by
-- proof
  apply StatMech.KingmanFilling.integrable_gLow h hnn

/--
[gLow_orbit_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gLow_orbit_mono_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, ∀ i j, i ≤ j → gLow T X (T^[i] x) ≤ gLow T X (T^[j] x) := by
-- proof
  apply StatMech.KingmanFilling.gLow_orbit_mono h hnn

/--
[nullMeasurableSet_badSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma nullMeasurableSet_badSet_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ε : ℝ}
  {N : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  NullMeasurableSet (badSet T X ε N) μ := by
-- proof
  apply StatMech.KingmanFilling.nullMeasurableSet_badSet h ε N

/--
[integrable_dep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma integrable_dep_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ε : ℝ}
  {N : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  Integrable (dep T X ε N) μ := by
-- proof
  apply StatMech.KingmanFilling.integrable_dep h hnn ε N

/--
[integrable_badCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma integrable_badCost_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ε : ℝ}
  {N : ℕ}
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  Integrable (badCost T X ε N) μ := by
-- proof
  apply StatMech.KingmanFilling.integrable_badCost h ε N

/--
[gStarLow_finite_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gStarLow_finite_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, gStarLow T X x ≠ ⊥ ∧ gStarLow T X x ≠ ⊤ := by
-- proof
  apply StatMech.KingmanFilling.gStarLow_finite_ae h hnn

/--
[exists_good](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma exists_good_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ε : ℝ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
  (hε : 0 < ε) :
-- imply
  ∀ᵐ x ∂μ, ∃ m, 1 ≤ m ∧ X m x ≤ (gLow T X x + ε) * m := by
-- proof
  apply StatMech.KingmanFilling.exists_good h hnn hε

/--
[tendsto_integral_badCost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma tendsto_integral_badCost_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ε : ℝ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
  (hε : 0 < ε) :
-- imply
  Tendsto (fun N => ∫ x, badCost T X ε N x ∂μ) atTop (𝓝 0) := by
-- proof
  apply StatMech.KingmanFilling.tendsto_integral_badCost h hnn hε

/--
[ae_all_subadditive_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma ae_all_subadditive_orbit_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X) :
-- imply
  ∀ᵐ x ∂μ, ∀ s a b, X (a + b) (T^[s] x) ≤ X a (T^[s] x) + X b (T^[a + s] x) := by
-- proof
  apply StatMech.KingmanFilling.ae_all_subadditive_orbit h

/--
[ae_orbit_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma ae_orbit_nonneg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, (∀ i, 0 ≤ gLow T X (T^[i] x)) ∧ (∀ i, 0 ≤ X 1 (T^[i] x)) := by
-- proof
  apply StatMech.KingmanFilling.ae_orbit_nonneg h hnn

/--
[per_n_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma per_n_integral_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ε : ℝ}
  {N : ℕ}
  {n : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
  (hε : 0 ≤ ε)
  (hN : 1 ≤ N) :
-- imply
  SubadditiveCocycle.expSeq X μ n ≤ n * (∫ x, dep T X ε N x ∂μ) + (N + 1) * ∫ x, remDom X N x ∂μ := by
-- proof
  apply StatMech.KingmanFilling.per_n_integral h hnn hε hN n

/--
[integral_dep_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma integral_dep_eq_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ε : ℝ}
  {N : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∫ x, dep T X ε N x ∂μ = (∫ x, gLow T X x ∂μ) + ε * (μ Set.univ).toReal + ∫ x, badCost T X ε N x ∂μ := by
-- proof
  apply StatMech.KingmanFilling.integral_dep_eq h hnn ε N

/--
[gamma_le_integral_dep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gamma_le_integral_dep_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ε : ℝ}
  {N : ℕ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
  (hε : 0 ≤ ε)
  (hN : 1 ≤ N) :
-- imply
  h.gamma ≤ ∫ x, dep T X ε N x ∂μ := by
-- proof
  apply StatMech.KingmanFilling.gamma_le_integral_dep h hnn hε hN

/--
[gamma_le_integral_gLow_add_eps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gamma_le_integral_gLow_add_eps_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
  {ε : ℝ}
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
  (hε : 0 < ε) :
-- imply
  h.gamma ≤ (∫ x, gLow T X x ∂μ) + ε * (μ Set.univ).toReal := by
-- proof
  apply StatMech.KingmanFilling.gamma_le_integral_gLow_add_eps h hnn hε

/--
[gamma_le_integral_gLow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gamma_le_integral_gLow_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  h.gamma ≤ ∫ x, gLow T X x ∂μ := by
-- proof
  apply StatMech.KingmanFilling.gamma_le_integral_gLow h hnn

/--
[gStar_le_gStarLow_ae_of_gamma_le_integral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gStar_le_gStarLow_ae_of_gamma_le_integral_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n)
  (hgamma : h.gamma ≤ ∫ x, gLow T X x ∂μ) :
-- imply
  ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x := by
-- proof
  apply StatMech.KingmanFilling.gStar_le_gStarLow_ae_of_gamma_le_integral h hnn hgamma

/--
[gStar_le_gStarLow_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma gStar_le_gStarLow_ae_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, gStar T X x ≤ gStarLow T X x := by
-- proof
  apply StatMech.KingmanFilling.gStar_le_gStarLow_ae h hnn

/--
[tendsto_div_kingmanLimit_ae_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/KingmanFilling.lean)
-/
@[path]
private lemma tendsto_div_kingmanLimit_ae_of_nonneg_eq
  [MeasurableSpace α]
  {μ : Measure α}
  {T : α → α}
  {X : ℕ → α → ℝ}
  [IsFiniteMeasure μ]
-- given
  (h : SubadditiveCocycle T μ X)
  (hnn : ∀ n, 0 ≤ᵐ[μ] X n) :
-- imply
  ∀ᵐ x ∂μ, Tendsto (fun n => X n x / n) atTop (𝓝 (kingmanLimit T X x)) := by
-- proof
  apply StatMech.KingmanFilling.tendsto_div_kingmanLimit_ae_of_nonneg h hnn


-- created on 2026-10-23
