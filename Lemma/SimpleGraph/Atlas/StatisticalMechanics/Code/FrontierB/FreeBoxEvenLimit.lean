import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
open MeasureTheory Filter Topology StatMech StatMech.FrontierB


/--
[isingExpectation_spinProd_mono_graph](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma isingExpectation_spinProd_mono_graph_eq
  [Fintype V]
  [DecidableEq V]
  {G H : SimpleGraph V}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {A : Finset V}
-- given
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hGH : G ≤ H) :
-- imply
  isingExpectation G beta h (spinProd A) ≤ isingExpectation H beta h (spinProd A) := by
-- proof
  apply StatMech.FrontierB.isingExpectation_spinProd_mono_graph G H beta h hbeta hh hGH A

/--
[isingExpectation_spinProd_induce_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma isingExpectation_spinProd_induce_le_eq
  [Fintype V]
  [DecidableEq V]
  {K : SimpleGraph V}
  [DecidableRel K.Adj]
  [DecidablePred P]
  {A : Finset {u // P u}}
-- given
  (P : V → Prop)
  (beta h : ℝ)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  isingExpectation (K.comap (Subtype.val : {u // P u} → V)) beta h (spinProd A) ≤ isingExpectation K beta h (spinProd (A.map (Function.Embedding.subtype P))) := by
-- proof
  apply StatMech.FrontierB.isingExpectation_spinProd_induce_le K P beta h hbeta hh A

/--
[spinProd_glue_eq_boxSpinSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma spinProd_glue_eq_boxSpinSupport_eq
  [Fintype V]
  [DecidableEq V]
  {d n : ℕ}
  {A : Finset (Site d)}
  {tau : ConfigSpace (sctBox d n)}
-- given
  (hA : ↑A ⊆ box d n) :
-- imply
  spinProd A (glue (minusField d) tau) = spinProd (boxSpinSupport d n A) tau := by
-- proof
  apply StatMech.FrontierB.spinProd_glue_eq_boxSpinSupport d n A hA tau

/--
[integral_freeMeasure_spinProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma integral_freeMeasure_spinProd_eq
  [Fintype V]
  [DecidableEq V]
  {d n : ℕ}
  {A : Finset (Site d)}
-- given
  (beta h : ℝ)
  (hA : ↑A ⊆ box d n) :
-- imply
  ∫ omega, spinProd A omega ∂(freeMeasure d n beta h : Measure (ConfigSpace (Site d))) = isingExpectation (sctBoxGraph d n) beta h (spinProd (boxSpinSupport d n A)) := by
-- proof
  apply StatMech.FrontierB.integral_freeMeasure_spinProd d n beta h A hA

/--
[boxSpinSupport_map_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma boxSpinSupport_map_inclusion_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {n m : ℕ}
  {A : Finset (Site d)}
-- given
  (hnm : n ≤ m)
  (hA : ↑A ⊆ box d n) :
-- imply
  ((boxSpinSupport d n A).map (sctBoxInclusionEquiv d hnm).toEmbedding).map (Function.Embedding.subtype (sctBoxInLarger d n m)) = boxSpinSupport d m A := by
-- proof
  apply StatMech.FrontierB.boxSpinSupport_map_inclusion d hnm A hA

/--
[isingExpectation_boxSpinSupport_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma isingExpectation_boxSpinSupport_mono_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {n m : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hnm : n ≤ m)
  (hbeta : 0 ≤ beta)
  (hA : ↑A ⊆ box d n) :
-- imply
  isingExpectation (sctBoxGraph d n) beta 0 (spinProd (boxSpinSupport d n A)) ≤ isingExpectation (sctBoxGraph d m) beta 0 (spinProd (boxSpinSupport d m A)) := by
-- proof
  apply StatMech.FrontierB.isingExpectation_boxSpinSupport_mono d hnm beta hbeta A hA

/--
[isingExpectation_spinProd_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma isingExpectation_spinProd_le_one_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {A : Finset V}
-- given
  (beta h : ℝ) :
-- imply
  isingExpectation G beta h (spinProd A) ≤ 1 := by
-- proof
  apply StatMech.FrontierB.isingExpectation_spinProd_le_one G beta h A

/--
[continuous_spinProd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma continuous_spinProd_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {A : Finset (Site d)} :
-- imply
  Continuous (spinProd A : ConfigSpace (Site d) → ℝ) := by
-- proof
  apply StatMech.FrontierB.continuous_spinProd A

/--
[spinProdBCF_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma spinProdBCF_apply_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {A : Finset (Site d)}
  {omega : ConfigSpace (Site d)} :
-- imply
  spinProdBCF d A omega = spinProd A omega := by
-- proof
  apply StatMech.FrontierB.spinProdBCF_apply d A omega

/--
[integral_freeMeasure_spinProd_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma integral_freeMeasure_spinProd_tendsto_freeState_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Tendsto (fun n => ∫ omega, spinProd A omega ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, spinProd A omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.integral_freeMeasure_spinProd_tendsto_freeState d beta hbeta A

/--
[prod_bond_eq_spinProd_edgeBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma prod_bond_eq_spinProd_edgeBoundary_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq V]
  {F : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  (∏ e ∈ F, bond s e) = spinProd (edgeBoundary F) s := by
-- proof
  apply StatMech.FrontierB.prod_bond_eq_spinProd_edgeBoundary F hF s

/--
[exp_neg_edgeSpinSum_eq_spinProd_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma exp_neg_edgeSpinSum_eq_spinProd_sum_eq
  [Fintype V]
  [DecidableEq V]
  [DecidableEq V]
  {beta : ℝ}
  {F : Finset (Sym2 V)}
  {s : ConfigSpace V}
-- given
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  Real.exp (-beta * edgeSpinSum F s) = ∑ T ∈ F.powerset, edgeExpansionCoeff beta F T * spinProd (edgeBoundary (F \ T)) s := by
-- proof
  apply StatMech.FrontierB.exp_neg_edgeSpinSum_eq_spinProd_sum beta F hF s

/--
[integral_spinProd_sum_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma integral_spinProd_sum_tendsto_freeState_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
  {K : Finset I}
  {c : I → ℝ}
  {support : I → Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Tendsto (fun n => ∫ omega, ∑ i ∈ K, c i * spinProd (support i) omega ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, ∑ i ∈ K, c i * spinProd (support i) omega ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.integral_spinProd_sum_tendsto_freeState d beta hbeta K c support

/--
[integral_exp_neg_edgeSpinSum_tendsto_freeState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma integral_exp_neg_edgeSpinSum_tendsto_freeState_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 ≤ beta)
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  Tendsto (fun n => ∫ s, Real.exp (-beta * edgeSpinSum F s) ∂(freeMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ s, Real.exp (-beta * edgeSpinSum F s) ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.integral_exp_neg_edgeSpinSum_tendsto_freeState d beta hbeta F hF

/--
[spinProd_eq_plusSpinExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma spinProd_eq_plusSpinExpansion_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {A : Finset (Site d)}
  {omega : ConfigSpace (Site d)} :
-- imply
  spinProd A omega = ∑ T ∈ A.powerset, plusSpinExpansionCoeff A T * iti_monomialBcf T omega := by
-- proof
  apply StatMech.FrontierB.spinProd_eq_plusSpinExpansion A omega

/--
[integral_plusMeasure_spinProd_full_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma integral_plusMeasure_spinProd_full_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
  {A : Finset (Site d)}
-- given
  (hbeta : 0 ≤ beta) :
-- imply
  Tendsto (fun n => ∫ omega, spinProd A omega ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, spinProd A omega ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.integral_plusMeasure_spinProd_full_tendsto d beta hbeta A

/--
[integral_plusMeasure_exp_neg_edgeSpinSum_full_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeBoxEvenLimit.lean)
-/
@[path]
private lemma integral_plusMeasure_exp_neg_edgeSpinSum_full_tendsto_eq
  [Fintype V]
  [DecidableEq V]
  {d : ℕ}
  {beta : ℝ}
  {F : Finset (Sym2 (Site d))}
-- given
  (hbeta : 0 ≤ beta)
  (hF : ∀ e ∈ F, ¬ e.IsDiag) :
-- imply
  Tendsto (fun n => ∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(plusMeasure d n beta 0 : Measure (ConfigSpace (Site d)))) atTop (nhds (∫ omega, Real.exp (-beta * edgeSpinSum F omega) ∂(plusState d beta 0 : Measure (ConfigSpace (Site d))))) := by
-- proof
  apply StatMech.FrontierB.integral_plusMeasure_exp_neg_edgeSpinSum_full_tendsto d beta hbeta F hF


-- created on 2026-10-23
