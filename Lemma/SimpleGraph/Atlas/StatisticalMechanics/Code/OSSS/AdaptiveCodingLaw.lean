import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.OSSS.AdaptiveCodingLaw.Part3
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCodingLaw


/--
[order_eq_on_prefix](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma order_eq_on_prefix_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {x y : ConfigSpace E}
  {m : ℕ}
-- given
  (hσ : PredictableOrder σ)
  (hm : m ≤ n)
  (hxy : Agree (prefixSet (σ x : Fin n → E) m) x y) :
-- imply
  ∀ (i : ℕ) (hi : i < m), (σ y : Fin n → E) ⟨i, lt_of_lt_of_le hi hm⟩ = (σ x : Fin n → E) ⟨i, lt_of_lt_of_le hi hm⟩ := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.order_eq_on_prefix hσ hm hxy

/--
[prefixSet_eq_of_predictable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma prefixSet_eq_of_predictable_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {x y : ConfigSpace E}
  {m : ℕ}
-- given
  (hσ : PredictableOrder σ)
  (hm : m ≤ n)
  (hxy : Agree (prefixSet (σ x : Fin n → E) m) x y) :
-- imply
  prefixSet (σ y : Fin n → E) m = prefixSet (σ x : Fin n → E) m := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.prefixSet_eq_of_predictable hσ hm hxy

/--
[codeMap_eq_unique_of_predictable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma codeMap_eq_unique_of_predictable_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {u : Fin n → ℝ}
  {x y : ConfigSpace E}
-- given
  (hσ : PredictableOrder σ)
  (hx : codeMap μ (σ x : Fin n → E) u = x)
  (hy : codeMap μ (σ y : Fin n → E) u = y) :
-- imply
  x = y := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.codeMap_eq_unique_of_predictable μ σ hσ u hx hy

/--
[predictable_fibres_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma predictable_fibres_disjoint_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {x y : ConfigSpace E}
-- given
  (hσ : PredictableOrder σ)
  (hxy : x ≠ y) :
-- imply
  Disjoint {u | codeMap μ (σ x : Fin n → E) u = x} {u | codeMap μ (σ y : Fin n → E) u = y} := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.predictable_fibres_disjoint μ σ hσ hxy

/--
[measurableSet_adaptiveFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma measurableSet_adaptiveFibre_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {x : ConfigSpace E} :
-- imply
  MeasurableSet (adaptiveFibre μ σ x) := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.measurableSet_adaptiveFibre μ σ x

/--
[vcube_adaptiveFibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma vcube_adaptiveFibre_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ((Vcube n) (adaptiveFibre μ σ x)).toReal = μ x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.vcube_adaptiveFibre μ hpos hμ1 σ x

/--
[predictable_adaptive_fibres_full_measure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma predictable_adaptive_fibres_full_measure_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  ((Vcube n) (⋃ x, adaptiveFibre μ σ x)).toReal = 1 := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.predictable_adaptive_fibres_full_measure μ hpos hμ1 σ hσ

/--
[adaptiveCode_eq_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma adaptiveCode_eq_of_mem_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {u : Fin n → ℝ}
  {x : ConfigSpace E}
-- given
  (hσ : PredictableOrder σ)
  (hx : u ∈ adaptiveFibre μ σ x) :
-- imply
  adaptiveCode μ σ u = x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.adaptiveCode_eq_of_mem μ σ hσ u x hx

/--
[measurableSet_adaptiveFibre_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma measurableSet_adaptiveFibre_union_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)} :
-- imply
  MeasurableSet (⋃ x, adaptiveFibre μ σ x) := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.measurableSet_adaptiveFibre_union μ σ

/--
[ae_mem_adaptiveFibre_union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma ae_mem_adaptiveFibre_union_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  ∀ᵐ u ∂(Vcube n), u ∈ ⋃ x, adaptiveFibre μ σ x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.ae_mem_adaptiveFibre_union μ hpos hμ1 σ hσ

/--
[adaptiveCode_eq_iff_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma adaptiveCode_eq_iff_ae_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  ∀ᵐ u ∂(Vcube n), adaptiveCode μ σ u = x ↔ u ∈ adaptiveFibre μ σ x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.adaptiveCode_eq_iff_ae μ hpos hμ1 σ hσ x

/--
[codeMap_selectedOrder_eq_adaptiveCode_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma codeMap_selectedOrder_eq_adaptiveCode_ae_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  ∀ᵐ u ∂(Vcube n), codeMap μ (σ (adaptiveCode μ σ u) : Fin n → E) u = adaptiveCode μ σ u := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.codeMap_selectedOrder_eq_adaptiveCode_ae μ hpos hμ1 σ hσ

/--
[adaptiveCode_fibre_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma adaptiveCode_fibre_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {x : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  ((Vcube n) {u | adaptiveCode μ σ u = x}).toReal = μ x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.adaptiveCode_fibre_mass μ hpos hμ1 σ hσ x

/--
[observable_adaptiveCode_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma observable_adaptiveCode_ae_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  (fun u => g (adaptiveCode μ σ u)) =ᵐ[Vcube n] (fun u => ∑ x, g x * Set.indicator (adaptiveFibre μ σ x) (fun _ => (1 : ℝ)) u) := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.observable_adaptiveCode_ae μ hpos hμ1 σ hσ g

/--
[aestronglyMeasurable_observable_adaptiveCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma aestronglyMeasurable_observable_adaptiveCode_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  AEStronglyMeasurable (fun u => g (adaptiveCode μ σ u)) (Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.aestronglyMeasurable_observable_adaptiveCode μ hpos hμ1 σ hσ g

/--
[integral_g_adaptiveCode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma integral_g_adaptiveCode_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  ∫ u, g (adaptiveCode μ σ u) ∂(Vcube n) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.integral_g_adaptiveCode μ hpos hμ1 σ hσ g

/--
[integral_g_adaptiveCode_Wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma integral_g_adaptiveCode_Wt_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {g : ConfigSpace E → ℝ}
  {s : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  ∫ p, g (adaptiveCode μ σ (Wt p.1 p.2 s)) ∂((Vcube n).prod (Vcube n)) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.integral_g_adaptiveCode_Wt μ hpos hμ1 σ hσ g s

/--
[integral_g_independent_randomOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma integral_g_independent_randomOrder_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {order : (Fin n → ℝ) → (Fin n ≃ E)}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ U, (∫ V, g (codeMap μ (order U : Fin n → E) V) ∂(Vcube n)) ∂(Vcube n) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.integral_g_independent_randomOrder μ hpos hμ1 order g

/--
[integral_g_frozenOrder_Wt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma integral_g_frozenOrder_Wt_zero_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hσ : PredictableOrder σ) :
-- imply
  ∫ U, (∫ V, g (codeMap μ (σ (adaptiveCode μ σ U) : Fin n → E) (Wt U V 0)) ∂(Vcube n)) ∂(Vcube n) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.integral_g_frozenOrder_Wt_zero μ hpos hμ1 σ hσ g

/--
[integral_g_frozenOrder_Wt_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCodingLaw.lean)
-/
@[path]
private lemma integral_g_frozenOrder_Wt_card_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {n : ℕ}
  {σ : ConfigSpace E → (Fin n ≃ E)}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∫ U, (∫ V, g (codeMap μ (σ (adaptiveCode μ σ U) : Fin n → E) (Wt U V n)) ∂(Vcube n)) ∂(Vcube n) = ∑ x, g x * μ x := by
-- proof
  apply StatMech.OSSS.AdaptiveCodingLaw.integral_g_frozenOrder_Wt_card μ hpos hμ1 σ g


-- created on 2026-10-23
