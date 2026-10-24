import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.OSSS.AdaptiveCausalKernel
open MeasureTheory StatMech StatMech.OSSS StatMech.OSSS.AdaptiveCausalKernel


/--
[realizedList_toFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realizedList_toFinset_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E} :
-- imply
  (realizedList S base).toFinset = R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedList_toFinset S base

/--
[realizedList_nodup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realizedList_nodup_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E} :
-- imply
  (realizedList S base).Nodup := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedList_nodup S base

/--
[realizedList_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realizedList_length_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E} :
-- imply
  (realizedList S base).length = R.card := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedList_length S base

/--
[realizedEquiv_symm_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realizedEquiv_symm_val_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {e : E} :
-- imply
  ((realizedEquiv S base).symm e : ℕ) = (realizedList S base).idxOf e := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedEquiv_symm_val S base e

/--
[prefixSet_realizedEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma prefixSet_realizedEquiv_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {e : E} :
-- imply
  prefixSet (realizedEquiv S base : Fin (Fintype.card E) → E) ((realizedEquiv S base).symm e : ℕ) = ((realizedList S base).take ((realizedList S base).idxOf e)).toFinset := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.prefixSet_realizedEquiv S base e

/--
[thr_realizedEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma thr_realizedEquiv_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : CausalOrder (Finset.univ : Finset E)}
  {base target : ConfigSpace E}
  {e : E} :
-- imply
  thr μ (realizedEquiv S base : Fin (Fintype.card E) → E) target ((realizedEquiv S base).symm e) = condProbClosed μ ((realizedList S base).take ((realizedList S base).idxOf e)).toFinset target e := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.thr_realizedEquiv μ S base target e

/--
[frozenCodeAtom_eq_rawPairBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma frozenCodeAtom_eq_rawPairBox_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : CausalOrder (Finset.univ : Finset E)}
  {base target : ConfigSpace E} :
-- imply
  frozenCodeAtom mu S base target = Set.univ.pi (frozenRawPair mu S base target) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.frozenCodeAtom_eq_rawPairBox mu S base target

/--
[pairedCube_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_measurePreserving_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  MeasurePreserving (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n)) (pairedCube n) ((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_measurePreserving n

/--
[pairedCube_integral_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_integral_equiv_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {g : (Fin n → ℝ) × (Fin n → ℝ) → ℝ} :
-- imply
  (∫ z, g (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n) z) ∂(pairedCube n)) = ∫ p, g p ∂((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_integral_equiv n g

/--
[pairedCube_frozenCodeAtom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_frozenCodeAtom_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : CausalOrder (Finset.univ : Finset E)}
  {base target : ConfigSpace E} :
-- imply
  pairedCube (Fintype.card E) (frozenCodeAtom mu S base target) = ∏ i : Fin (Fintype.card E), ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) (frozenRawPair mu S base target i) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_frozenCodeAtom mu S base target

/--
[realizedList_leftOrder_eq_rightOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realizedList_leftOrder_eq_rightOrder_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : TripleOrder R}
  {base : ConfigSpace E} :
-- imply
  realizedList S.leftOrder base = realizedList S.rightOrder base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedList_leftOrder_eq_rightOrder S base

/--
[realizedEquiv_leftOrder_eq_rightOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realizedEquiv_leftOrder_eq_rightOrder_eq
  [Fintype E]
  [DecidableEq E]
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E} :
-- imply
  realizedEquiv S.leftOrder base = realizedEquiv S.rightOrder base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedEquiv_leftOrder_eq_rightOrder S base

/--
[independentAt_leftOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma independentAt_leftOrder_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : TripleOrder R}
  {base : ConfigSpace E}
  {z : E} :
-- imply
  independentAt S.leftOrder base z = (tripleModeAt S base z).leftIndependent := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.independentAt_leftOrder S base z

/--
[independentAt_rightOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma independentAt_rightOrder_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : TripleOrder R}
  {base : ConfigSpace E}
  {z : E} :
-- imply
  independentAt S.rightOrder base z = (tripleModeAt S base z).rightIndependent := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.independentAt_rightOrder S base z

/--
[causalMixLabels_leftOrder_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalMixLabels_leftOrder_apply_eq
  [Fintype E]
  [DecidableEq E]
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {U V : Fin (Fintype.card E) → ℝ}
  {i : Fin (Fintype.card E)} :
-- imply
  causalMixLabels S.leftOrder base U V i = match tripleModeAt S base (realizedEquiv S.leftOrder base i) with := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalMixLabels_leftOrder_apply S base U V i

/--
[causalMixLabels_rightOrder_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalMixLabels_rightOrder_apply_eq
  [Fintype E]
  [DecidableEq E]
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {U V : Fin (Fintype.card E) → ℝ}
  {i : Fin (Fintype.card E)} :
-- imply
  causalMixLabels S.rightOrder base U V i = match tripleModeAt S base (realizedEquiv S.rightOrder base i) with := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalMixLabels_rightOrder_apply S base U V i

/--
[causalMixLabels_left_eq_right_of_mode_ne_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalMixLabels_left_eq_right_of_mode_ne_flip_eq
  [Fintype E]
  [DecidableEq E]
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {U V : Fin (Fintype.card E) → ℝ}
  {i : Fin (Fintype.card E)}
-- given
  (hmode : tripleModeAt S base (realizedEquiv S.leftOrder base i) ≠ .flip) :
-- imply
  causalMixLabels S.leftOrder base U V i = causalMixLabels S.rightOrder base U V i := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalMixLabels_left_eq_right_of_mode_ne_flip S base U V i hmode

/--
[causalMixLabels_leftOrder_eq_rightOrder_of_no_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalMixLabels_leftOrder_eq_rightOrder_of_no_flip_eq
  [Fintype E]
  [DecidableEq E]
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {U V : Fin (Fintype.card E) → ℝ}
-- given
  (hno : ∀ e, tripleModeAt S base e ≠ .flip) :
-- imply
  causalMixLabels S.leftOrder base U V = causalMixLabels S.rightOrder base U V := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalMixLabels_leftOrder_eq_rightOrder_of_no_flip S base hno U V

/--
[measurable_causalMixLabels_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma measurable_causalMixLabels_right_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {U : Fin (Fintype.card E) → ℝ} :
-- imply
  Measurable (fun V => causalMixLabels S base U V) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.measurable_causalMixLabels_right S base U

/--
[measurable_causalMixLabels_prod](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma measurable_causalMixLabels_prod_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E} :
-- imply
  Measurable (fun p : (Fin (Fintype.card E) → ℝ) × (Fin (Fintype.card E) → ℝ) => causalMixLabels S base p.1 p.2) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.measurable_causalMixLabels_prod S base

/--
[causalMixLabels_mono_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalMixLabels_mono_right_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {U : Fin (Fintype.card E) → ℝ} :
-- imply
  Monotone (fun V => causalMixLabels S base U V) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalMixLabels_mono_right S base U

/--
[measurable_pairedCausalOutputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma measurable_pairedCausalOutputs_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E} :
-- imply
  Measurable (pairedCausalOutputs mu S base) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.measurable_pairedCausalOutputs mu S base

/--
[pairedCausalOutputs_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCausalOutputs_fibre_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E} :
-- imply
  {z | pairedCausalOutputs mu S base z = (base, left, right)} = frozenTripleCodeAtom mu S base left right := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCausalOutputs_fibre mu S base left right

/--
[frozenTripleCodeAtom_eq_rawPairBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma frozenTripleCodeAtom_eq_rawPairBox_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E} :
-- imply
  frozenTripleCodeAtom mu S base left right = Set.univ.pi (frozenTripleRawPair mu S base left right) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.frozenTripleCodeAtom_eq_rawPairBox mu S base left right

/--
[pairedCube_frozenTripleCodeAtom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_frozenTripleCodeAtom_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E} :
-- imply
  pairedCube (Fintype.card E) (frozenTripleCodeAtom mu S base left right) = ∏ i : Fin (Fintype.card E), ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) (frozenTripleRawPair mu S base left right i) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_frozenTripleCodeAtom mu S base left right

/--
[tripleModeAt_beforeOfCausal_ne_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleModeAt_beforeOfCausal_ne_flip_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E}
  {z : E} :
-- imply
  tripleModeAt (TripleOrder.beforeOfCausal S) base z ≠ .flip := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleModeAt_beforeOfCausal_ne_flip S base z

/--
[tripleModeAt_extendDecisionTreeTriple_none_ne_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleModeAt_extendDecisionTreeTriple_none_ne_flip_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E}
  {z : E} :
-- imply
  tripleModeAt (extendDecisionTreeTriple none T known R) base z ≠ .flip := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleModeAt_extendDecisionTreeTriple_none_ne_flip T known base R z

/--
[tripleModeAt_extendDecisionTreeTriple_flip_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleModeAt_extendDecisionTreeTriple_flip_unique_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E}
  {x y : E}
-- given
  (hx : tripleModeAt (extendDecisionTreeTriple (some t) T known R) base x = .flip)
  (hy : tripleModeAt (extendDecisionTreeTriple (some t) T known R) base y = .flip) :
-- imply
  x = y := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleModeAt_extendDecisionTreeTriple_flip_unique t T known base R x y hx hy

/--
[causal_abs_eq_four_terms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causal_abs_eq_four_terms_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
  {t : ℕ}
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {U V : Fin (Fintype.card E) → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (he : tripleModeAt (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e = .flip) :
-- imply
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E) let σ := realizedEquiv S.leftOrder base let Yl := codeMap μ (σ : Fin (Fintype.card E) → E) (causalMixLabels S.leftOrder base U V) let Yr := codeMap μ (σ : Fin (Fintype.card E) → E) (causalMixLabels S.rightOrder base U V) |f Yr - f Yl| = f Yl * Lindeberg.coord e Yl + f Yr * Lindeberg.coord e Yr - f Yl * Lindeberg.coord e Yr - f Yr * Lindeberg.coord e Yl := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causal_abs_eq_four_terms hpos hmono hf t T base U V e he

/--
[TripleOrder.leftOrder_beforeOfCausal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma leftOrder_beforeOfCausal_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R} :
-- imply
  (TripleOrder.beforeOfCausal S).leftOrder = allIndependent S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.TripleOrder.leftOrder_beforeOfCausal S

/--
[TripleOrder.rightOrder_beforeOfCausal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma rightOrder_beforeOfCausal_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R} :
-- imply
  (TripleOrder.beforeOfCausal S).rightOrder = allIndependent S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.TripleOrder.rightOrder_beforeOfCausal S

/--
[sharedEdges_allIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_allIndependent_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E} :
-- imply
  sharedEdges (allIndependent S) base = ∅ := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_allIndependent S base

/--
[allIndependent_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma allIndependent_cast_eq
  [Fintype E]
  [DecidableEq E]
  {R S : Finset E}
  {C : CausalOrder R}
-- given
  (h : R = S) :
-- imply
  allIndependent (h ▸ C) = h ▸ allIndependent C := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.allIndependent_cast h C

/--
[allIndependent_fixedListOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma allIndependent_fixedListOrder_eq
  [Fintype E]
  [DecidableEq E]
  {l : List E}
-- given
  (h : l.Nodup) :
-- imply
  allIndependent (fixedListOrder l h) = fixedListOrder l h := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.allIndependent_fixedListOrder l h

/--
[allIndependent_fixedOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma allIndependent_fixedOrder_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E} :
-- imply
  allIndependent (fixedOrder R) = fixedOrder R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.allIndependent_fixedOrder R

/--
[sharedEdges_cast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_cast_eq
  [Fintype E]
  [DecidableEq E]
  {R S : Finset E}
  {C : CausalOrder R}
  {base : ConfigSpace E}
-- given
  (h : R = S) :
-- imply
  sharedEdges (h ▸ C) base = sharedEdges C base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_cast h C base

/--
[sharedEdges_fixedListOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_fixedListOrder_eq
  [Fintype E]
  [DecidableEq E]
  {l : List E}
  {base : ConfigSpace E}
-- given
  (h : l.Nodup) :
-- imply
  sharedEdges (fixedListOrder l h) base = ∅ := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_fixedListOrder l h base

/--
[sharedEdges_fixedOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_fixedOrder_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {base : ConfigSpace E} :
-- imply
  sharedEdges (fixedOrder R) base = ∅ := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_fixedOrder R base

/--
[sharedEdges_extendDecisionTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_extendDecisionTree_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E}
-- given
  (hknown : ∀ z, z ∉ R → known z = base z) :
-- imply
  sharedEdges (extendDecisionTree T known R) base = T.queried base ∩ R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_extendDecisionTree T known base R hknown

/--
[sharedEdges_extendDecisionTree_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_extendDecisionTree_univ_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {base : ConfigSpace E} :
-- imply
  sharedEdges (extendDecisionTree T base (Finset.univ : Finset E)) base = T.queried base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_extendDecisionTree_univ T base

/--
[mean_mem_sharedEdges_extendDecisionTree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma mean_mem_sharedEdges_extendDecisionTree_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {e : E} :
-- imply
  Lindeberg.mean μ (fun base => if e ∈ sharedEdges (extendDecisionTree T base (Finset.univ : Finset E)) base then (1 : ℝ) else 0) = LindebergTree.revealmentMu μ T e := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.mean_mem_sharedEdges_extendDecisionTree μ T e

/--
[extendDecisionTreeTriple_none_leftOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeTriple_none_leftOrder_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E} :
-- imply
  (extendDecisionTreeTriple none T known R).leftOrder = extendDecisionTreeAt 0 T known R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeTriple_none_leftOrder T known R

/--
[extendDecisionTreeTriple_none_rightOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeTriple_none_rightOrder_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E} :
-- imply
  (extendDecisionTreeTriple none T known R).rightOrder = extendDecisionTreeAt 0 T known R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeTriple_none_rightOrder T known R

/--
[card_insert_inter_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma card_insert_inter_sub_one_eq
  [Fintype E]
  [DecidableEq E]
  {P R : Finset E}
  {q : E}
-- given
  (hq : q ∈ R) :
-- imply
  (insert q P ∩ R).card - 1 = (P ∩ R.erase q).card := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.card_insert_inter_sub_one P R q hq

/--
[tripleModeAt_extendDecisionTreeTriple_eq_flip_of_fresh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleModeAt_extendDecisionTreeTriple_eq_flip_of_fresh_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {base known : ConfigSpace E}
  {R : Finset E}
  {t : ℕ}
  {e : E}
-- given
  (hknown : ∀ z, z ∉ R → known z = base z)
  (hq : PredictableTreeQuery.pathQuery T base t = some e)
  (hfresh : e ∉ LindebergTree.pathPrefix T base t)
  (heR : e ∈ R) :
-- imply
  tripleModeAt (extendDecisionTreeTriple (some ((LindebergTree.pathPrefix T base t ∩ R).card)) T known R) base e = .flip := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleModeAt_extendDecisionTreeTriple_eq_flip_of_fresh T base known R hknown t e hq hfresh heR

/--
[extendDecisionTreeTriple_leftOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeTriple_leftOrder_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E} :
-- imply
  (extendDecisionTreeTriple (some t) T known R).leftOrder = extendDecisionTreeAt t T known R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeTriple_leftOrder t T known R

/--
[extendDecisionTreeTriple_rightOrder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeTriple_rightOrder_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E} :
-- imply
  (extendDecisionTreeTriple (some t) T known R).rightOrder = extendDecisionTreeAt (t + 1) T known R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeTriple_rightOrder t T known R

/--
[extendDecisionTreeTriple_known_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeTriple_known_congr_eq
  [Fintype E]
  [DecidableEq E]
  {phase : Option ℕ}
  {T : DecisionTree E}
  {known known' : ConfigSpace E}
  {R : Finset E}
-- given
  (hknown : ∀ z, z ∉ R → known z = known' z) :
-- imply
  extendDecisionTreeTriple phase T known R = extendDecisionTreeTriple phase T known' R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeTriple_known_congr phase T known known' R hknown

/--
[extendDecisionTreeTriple_univ_seed_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeTriple_univ_seed_congr_eq
  [Fintype E]
  [DecidableEq E]
  {phase : Option ℕ}
  {T : DecisionTree E}
  {known known' : ConfigSpace E} :
-- imply
  extendDecisionTreeTriple phase T known (Finset.univ : Finset E) = extendDecisionTreeTriple phase T known' Finset.univ := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeTriple_univ_seed_congr phase T known known'

/--
[extendDecisionTreeAt_univ_seed_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeAt_univ_seed_congr_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known known' : ConfigSpace E} :
-- imply
  extendDecisionTreeAt t T known (Finset.univ : Finset E) = extendDecisionTreeAt t T known' Finset.univ := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeAt_univ_seed_congr t T known known'

/--
[extendDecisionTreeAt_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeAt_zero_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E} :
-- imply
  extendDecisionTreeAt 0 T known R = extendDecisionTree T known R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeAt_zero T known R

/--
[extendDecisionTreeAt_eq_allIndependent_of_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeAt_eq_allIndependent_of_card_le_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E}
-- given
  (hcard : R.card ≤ t) :
-- imply
  extendDecisionTreeAt t T known R = allIndependent (extendDecisionTree T known R) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeAt_eq_allIndependent_of_card_le t T known R hcard

/--
[extendDecisionTreeAt_card_univ_eq_allIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma extendDecisionTreeAt_card_univ_eq_allIndependent_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {known : ConfigSpace E} :
-- imply
  extendDecisionTreeAt (Fintype.card E) T known (Finset.univ : Finset E) = allIndependent (extendDecisionTree T known Finset.univ) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.extendDecisionTreeAt_card_univ_eq_allIndependent T known

/--
[sharedEdges_extendDecisionTreeAt_eq_empty_of_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_extendDecisionTreeAt_eq_empty_of_card_le_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E}
-- given
  (hknown : ∀ z, z ∉ R → known z = base z)
  (hcard : R.card ≤ t) :
-- imply
  sharedEdges (extendDecisionTreeAt t T known R) base = ∅ := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_extendDecisionTreeAt_eq_empty_of_card_le t T known base R hknown hcard

/--
[sharedEdges_extendDecisionTreeAt_card_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_extendDecisionTreeAt_card_univ_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {known base : ConfigSpace E} :
-- imply
  sharedEdges (extendDecisionTreeAt (Fintype.card E) T known (Finset.univ : Finset E)) base = ∅ := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_extendDecisionTreeAt_card_univ T known base

/--
[sharedEdges_extendDecisionTreeAt_succ_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_extendDecisionTreeAt_succ_subset_eq
  [Fintype E]
  [DecidableEq E]
  {t : ℕ}
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E}
-- given
  (hknown : ∀ z, z ∉ R → known z = base z) :
-- imply
  sharedEdges (extendDecisionTreeAt (t + 1) T known R) base ⊆ sharedEdges (extendDecisionTreeAt t T known R) base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_extendDecisionTreeAt_succ_subset t T known base R hknown

/--
[sharedStepIndicator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedStepIndicator_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {t : ℕ}
  {e : E} :
-- imply
  0 ≤ sharedStepIndicator T base t e := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedStepIndicator_nonneg T base t e

/--
[sum_sharedStepIndicator_eq_queried](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_sharedStepIndicator_eq_queried_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {e : E} :
-- imply
  ∑ t ∈ Finset.range (Fintype.card E), sharedStepIndicator T base t e = if e ∈ T.queried base then 1 else 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_sharedStepIndicator_eq_queried T base e

/--
[sum_mean_sharedStepIndicator_eq_revealmentMu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_mean_sharedStepIndicator_eq_revealmentMu_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {e : E} :
-- imply
  ∑ t ∈ Finset.range (Fintype.card E), Lindeberg.mean μ (fun base => sharedStepIndicator T base t e) = LindebergTree.revealmentMu μ T e := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_mean_sharedStepIndicator_eq_revealmentMu μ T e

/--
[sharedEdges_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedEdges_subset_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E} :
-- imply
  sharedEdges S base ⊆ R := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedEdges_subset S base

/--
[mem_sharedEdges_iff_independentAt_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma mem_sharedEdges_iff_independentAt_false_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E}
  {e : E}
-- given
  (he : e ∈ R) :
-- imply
  e ∈ sharedEdges S base ↔ independentAt S base e = false := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.mem_sharedEdges_iff_independentAt_false S base e he

/--
[sharedStepIndicator_eq_tripleFlipIndicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sharedStepIndicator_eq_tripleFlipIndicator_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {t : ℕ}
  {e : E} :
-- imply
  sharedStepIndicator T base t e = tripleFlipIndicator (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sharedStepIndicator_eq_tripleFlipIndicator T base t e

/--
[rawInterval_toReal_eq_bitWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma rawInterval_toReal_eq_bitWeight_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {n : ℕ}
  {sigma : Fin n → E}
  {x : ConfigSpace E}
  {i : Fin n}
-- given
  (hpos : ∀ omega, 0 < mu omega) :
-- imply
  (volume.restrict (Set.Icc (0 : ℝ) 1) (GrandCoupling.rawInterval mu sigma x i)).toReal = bitWeight (thr mu sigma x i) (x (sigma i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.rawInterval_toReal_eq_bitWeight mu hpos sigma x i

/--
[bitWeight_false_add_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma bitWeight_false_add_true_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ} :
-- imply
  bitWeight q false + bitWeight q true = 1 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.bitWeight_false_add_true q

/--
[independentWeight_sum_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma independentWeight_sum_base_eq
  [Fintype E]
  [DecidableEq E]
  {a q : ℝ}
  {target : Bool} :
-- imply
  independentWeight a q false target + independentWeight a q true target = bitWeight q target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.independentWeight_sum_base a q target

/--
[volume_thresholdInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma volume_thresholdInterval_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {b : Bool}
-- given
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1) :
-- imply
  (volume (thresholdInterval q b)).toReal = bitWeight q b := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.volume_thresholdInterval q hq0 hq1 b

/--
[volume_inter_threshold_false_add_true](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma volume_inter_threshold_false_add_true_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set ℝ}
  {q : ℝ}
-- given
  (hA : MeasurableSet A)
  (hAcube : A ⊆ Set.Ico (0 : ℝ) 1)
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1) :
-- imply
  (volume (A ∩ thresholdInterval q false)).toReal + (volume (A ∩ thresholdInterval q true)).toReal = (volume A).toReal := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.volume_inter_threshold_false_add_true A hA hAcube q hq0 hq1

/--
[volume_thresholdInterval_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma volume_thresholdInterval_inter_eq
  [Fintype E]
  [DecidableEq E]
  {a q : ℝ}
  {base target : Bool}
-- given
  (ha0 : 0 ≤ a)
  (ha1 : a ≤ 1)
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1) :
-- imply
  (volume (thresholdInterval a base ∩ thresholdInterval q target)).toReal = overlapWeight a q base target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.volume_thresholdInterval_inter a q ha0 ha1 hq0 hq1 base target

/--
[rawInterval_inter_toReal_eq_overlapWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma rawInterval_inter_toReal_eq_overlapWeight_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {n : ℕ}
  {sigma : Fin n → E}
  {base target : ConfigSpace E}
  {i : Fin n}
-- given
  (hpos : ∀ omega, 0 < mu omega) :
-- imply
  (volume.restrict (Set.Icc (0 : ℝ) 1) (GrandCoupling.rawInterval mu sigma base i ∩ GrandCoupling.rawInterval mu sigma target i)).toReal = overlapWeight (thr mu sigma base i) (thr mu sigma target i) (base (sigma i)) (target (sigma i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.rawInterval_inter_toReal_eq_overlapWeight mu hpos sigma base target i

/--
[rawInterval_tripleInter_toReal_eq_tripleOverlapWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma rawInterval_tripleInter_toReal_eq_tripleOverlapWeight_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {n : ℕ}
  {sigma : Fin n → E}
  {base left right : ConfigSpace E}
  {i : Fin n}
-- given
  (hpos : ∀ omega, 0 < mu omega) :
-- imply
  (volume.restrict (Set.Icc (0 : ℝ) 1) (GrandCoupling.rawInterval mu sigma base i ∩ GrandCoupling.rawInterval mu sigma left i ∩ GrandCoupling.rawInterval mu sigma right i)).toReal = (volume (thresholdInterval (thr mu sigma base i) (base (sigma i)) ∩ thresholdInterval (thr mu sigma left i) (left (sigma i)) ∩ thresholdInterval (thr mu sigma right i) (right (sigma i)))).toReal := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.rawInterval_tripleInter_toReal_eq_tripleOverlapWeight mu hpos sigma base left right i

/--
[frozenRawPair_toReal_eq_splitWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma frozenRawPair_toReal_eq_splitWeight_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : CausalOrder (Finset.univ : Finset E)}
  {base target : ConfigSpace E}
  {i : Fin (Fintype.card E)}
-- given
  (hpos : ∀ omega, 0 < mu omega) :
-- imply
  (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) (frozenRawPair mu S base target i)).toReal = splitWeight (independentAt S base (realizedEquiv S base i)) (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) base i) (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) target i) (base (realizedEquiv S base i)) (target (realizedEquiv S base i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.frozenRawPair_toReal_eq_splitWeight mu hpos S base target i

/--
[pairedCube_frozenCodeAtom_toReal_eq_prod_splitWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_frozenCodeAtom_toReal_eq_prod_splitWeight_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : CausalOrder (Finset.univ : Finset E)}
  {base target : ConfigSpace E}
-- given
  (hpos : ∀ omega, 0 < mu omega) :
-- imply
  (pairedCube (Fintype.card E) (frozenCodeAtom mu S base target)).toReal = ∏ i : Fin (Fintype.card E), splitWeight (independentAt S base (realizedEquiv S base i)) (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) base i) (thr mu (realizedEquiv S base : Fin (Fintype.card E) → E) target i) (base (realizedEquiv S base i)) (target (realizedEquiv S base i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_frozenCodeAtom_toReal_eq_prod_splitWeight mu hpos S base target

/--
[overlapWeight_sum_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma overlapWeight_sum_base_eq
  [Fintype E]
  [DecidableEq E]
  {a q : ℝ}
  {target : Bool} :
-- imply
  overlapWeight a q false target + overlapWeight a q true target = if target then 1 - q else q := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.overlapWeight_sum_base a q target

/--
[overlapWeight_same_threshold_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma overlapWeight_same_threshold_ne_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {b c : Bool}
-- given
  (hbc : b ≠ c) :
-- imply
  overlapWeight q q b c = 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.overlapWeight_same_threshold_ne q hbc

/--
[splitWeight_sum_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma splitWeight_sum_base_eq
  [Fintype E]
  [DecidableEq E]
  {independent : Bool}
  {a q : ℝ}
  {target : Bool} :
-- imply
  splitWeight independent a q false target + splitWeight independent a q true target = bitWeight q target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.splitWeight_sum_base independent a q target

/--
[overlapWeight_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma overlapWeight_comm_eq
  [Fintype E]
  [DecidableEq E]
  {a q : ℝ}
  {b c : Bool} :
-- imply
  overlapWeight a q b c = overlapWeight q a c b := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.overlapWeight_comm a q b c

/--
[frozenTripleRawPair_toReal_eq_tripleWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma frozenTripleRawPair_toReal_eq_tripleWeight_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E}
  {i : Fin (Fintype.card E)}
-- given
  (hpos : ∀ omega, 0 < mu omega) :
-- imply
  (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) (frozenTripleRawPair mu S base left right i)).toReal = tripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i)) (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i) (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i) (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i) (base (realizedEquiv S.leftOrder base i)) (left (realizedEquiv S.leftOrder base i)) (right (realizedEquiv S.leftOrder base i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.frozenTripleRawPair_toReal_eq_tripleWeight mu hpos S base left right i

/--
[pairedCube_frozenTripleCodeAtom_toReal_eq_prod_tripleWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_frozenTripleCodeAtom_toReal_eq_prod_tripleWeight_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E}
-- given
  (hpos : ∀ omega, 0 < mu omega) :
-- imply
  (pairedCube (Fintype.card E) (frozenTripleCodeAtom mu S base left right)).toReal = ∏ i : Fin (Fintype.card E), tripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i)) (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i) (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i) (thr mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i) (base (realizedEquiv S.leftOrder base i)) (left (realizedEquiv S.leftOrder base i)) (right (realizedEquiv S.leftOrder base i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_frozenTripleCodeAtom_toReal_eq_prod_tripleWeight mu hpos S base left right

/--
[thresholdInterval_subset_Ico](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma thresholdInterval_subset_Ico_eq
  [Fintype E]
  [DecidableEq E]
  {q : ℝ}
  {b : Bool}
-- given
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1) :
-- imply
  thresholdInterval q b ⊆ Set.Ico (0 : ℝ) 1 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.thresholdInterval_subset_Ico q hq0 hq1 b

/--
[tripleOverlapWeight_sum_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleOverlapWeight_sum_third_eq
  [Fintype E]
  [DecidableEq E]
  {a q r : ℝ}
  {b y : Bool}
-- given
  (ha0 : 0 ≤ a)
  (ha1 : a ≤ 1)
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1)
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1) :
-- imply
  tripleOverlapWeight a q r b y false + tripleOverlapWeight a q r b y true = overlapWeight a q b y := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleOverlapWeight_sum_third a q r ha0 ha1 hq0 hq1 hr0 hr1 b y

/--
[tripleOverlapWeight_sum_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleOverlapWeight_sum_second_eq
  [Fintype E]
  [DecidableEq E]
  {a q r : ℝ}
  {b z : Bool}
-- given
  (ha0 : 0 ≤ a)
  (ha1 : a ≤ 1)
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1)
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1) :
-- imply
  tripleOverlapWeight a q r b false z + tripleOverlapWeight a q r b true z = overlapWeight a r b z := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleOverlapWeight_sum_second a q r ha0 ha1 hq0 hq1 hr0 hr1 b z

/--
[tripleWeight_sum_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleWeight_sum_third_eq
  [Fintype E]
  [DecidableEq E]
  {mode : TripleMode}
  {a q r : ℝ}
  {b y : Bool}
-- given
  (ha0 : 0 ≤ a)
  (ha1 : a ≤ 1)
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1)
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1) :
-- imply
  tripleWeight mode a q r b y false + tripleWeight mode a q r b y true = splitWeight mode.leftIndependent a q b y := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleWeight_sum_third mode a q r ha0 ha1 hq0 hq1 hr0 hr1 b y

/--
[tripleWeight_sum_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleWeight_sum_second_eq
  [Fintype E]
  [DecidableEq E]
  {mode : TripleMode}
  {a q r : ℝ}
  {b z : Bool}
-- given
  (ha0 : 0 ≤ a)
  (ha1 : a ≤ 1)
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1)
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1) :
-- imply
  tripleWeight mode a q r b false z + tripleWeight mode a q r b true z = splitWeight mode.rightIndependent a r b z := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleWeight_sum_second mode a q r ha0 ha1 hq0 hq1 hr0 hr1 b z

/--
[measurable_tripleCausalOutputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma measurable_tripleCausalOutputs_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E} :
-- imply
  Measurable (tripleCausalOutputs μ S base) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.measurable_tripleCausalOutputs μ S base

/--
[tripleCausalOutputs_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCausalOutputs_fibre_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E} :
-- imply
  {z | tripleCausalOutputs μ S base z = (base, left, right)} = frozenCrossCodeAtom μ S base left right := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCausalOutputs_fibre μ S base left right

/--
[frozenCrossCodeAtom_eq_rawTripleBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma frozenCrossCodeAtom_eq_rawTripleBox_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E} :
-- imply
  frozenCrossCodeAtom μ S base left right = Set.univ.pi (crossRawTriple μ S base left right) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.frozenCrossCodeAtom_eq_rawTripleBox μ S base left right

/--
[tripleCube_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCube_measurePreserving_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  MeasurePreserving (fun z : Fin n → ((ℝ × ℝ) × ℝ) => ((fun i => (z i).1.1, fun i => (z i).1.2), fun i => (z i).2)) (tripleCube n) (((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod (GrandCoupling.Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCube_measurePreserving n

/--
[tripleCubeEquiv_measurePreserving](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCubeEquiv_measurePreserving_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ} :
-- imply
  MeasurePreserving (tripleCubeEquiv n) (tripleCube n) (((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod (GrandCoupling.Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCubeEquiv_measurePreserving n

/--
[tripleCube_integral_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCube_integral_equiv_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {g : (((Fin n → ℝ) × (Fin n → ℝ)) × (Fin n → ℝ)) → ℝ} :
-- imply
  (∫ z, g (tripleCubeEquiv n z) ∂(tripleCube n)) = ∫ p, g p ∂(((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod (GrandCoupling.Vcube n)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCube_integral_equiv n g

/--
[tripleCube_frozenCrossCodeAtom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCube_frozenCrossCodeAtom_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E} :
-- imply
  tripleCube (Fintype.card E) (frozenCrossCodeAtom μ S base left right) = ∏ i : Fin (Fintype.card E), let ν := volume.restrict (Set.Icc (0 : ℝ) 1) (ν.prod ν).prod ν (crossRawTriple μ S base left right i) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCube_frozenCrossCodeAtom μ S base left right

/--
[tripleLabelCube_frozenCrossRawAtom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleLabelCube_frozenCrossRawAtom_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E} :
-- imply
  tripleLabelCube (Fintype.card E) (frozenCrossRawAtom μ S base left right) = ∏ i : Fin (Fintype.card E), (((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Set.Icc (0 : ℝ) 1))).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) (crossRawTriple μ S base left right i) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleLabelCube_frozenCrossRawAtom μ S base left right

/--
[crossRawTriple_toReal_eq_crossTripleWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma crossRawTriple_toReal_eq_crossTripleWeight_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E}
  {i : Fin (Fintype.card E)}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  let ν := volume.restrict (Set.Icc (0 : ℝ) 1) ((ν.prod ν).prod ν (crossRawTriple μ S base left right i)).toReal = crossTripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i)) (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i) (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i) (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i) (base (realizedEquiv S.leftOrder base i)) (left (realizedEquiv S.leftOrder base i)) (right (realizedEquiv S.leftOrder base i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.crossRawTriple_toReal_eq_crossTripleWeight μ hpos S base left right i

/--
[overlapWeight_sum_target](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma overlapWeight_sum_target_eq
  [Fintype E]
  [DecidableEq E]
  {a q : ℝ}
  {base : Bool} :
-- imply
  overlapWeight a q base false + overlapWeight a q base true = bitWeight a base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.overlapWeight_sum_target a q base

/--
[crossTripleWeight_sum_third](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma crossTripleWeight_sum_third_eq
  [Fintype E]
  [DecidableEq E]
  {mode : TripleMode}
  {a q r : ℝ}
  {b y : Bool}
-- given
  (ha0 : 0 ≤ a)
  (ha1 : a ≤ 1)
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1)
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1) :
-- imply
  crossTripleWeight mode a q r b y false + crossTripleWeight mode a q r b y true = splitWeight mode.leftIndependent a q b y := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.crossTripleWeight_sum_third mode a q r ha0 ha1 hq0 hq1 hr0 hr1 b y

/--
[crossTripleWeight_sum_second](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma crossTripleWeight_sum_second_eq
  [Fintype E]
  [DecidableEq E]
  {mode : TripleMode}
  {a q r : ℝ}
  {b z : Bool}
-- given
  (ha0 : 0 ≤ a)
  (ha1 : a ≤ 1)
  (hq0 : 0 ≤ q)
  (hq1 : q ≤ 1)
  (hr0 : 0 ≤ r)
  (hr1 : r ≤ 1) :
-- imply
  crossTripleWeight mode a q r b false z + crossTripleWeight mode a q r b true z = splitWeight mode.rightIndependent a r b z := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.crossTripleWeight_sum_second mode a q r ha0 ha1 hq0 hq1 hr0 hr1 b z

/--
[tripleRealizedSchedule_map_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleRealizedSchedule_map_fst_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : TripleOrder R}
  {base : ConfigSpace E} :
-- imply
  (tripleRealizedSchedule S base).map Prod.fst = realizedList S.leftOrder base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleRealizedSchedule_map_fst S base

/--
[tripleRealizedSchedule_mode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleRealizedSchedule_mode_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : TripleOrder R}
  {base : ConfigSpace E}
  {p : E × TripleMode}
-- given
  (hp : p ∈ tripleRealizedSchedule S base) :
-- imply
  p.2 = tripleModeAt S base p.1 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleRealizedSchedule_mode S base p hp

/--
[idxOf_fst_tripleRealizedSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma idxOf_fst_tripleRealizedSchedule_eq
  [Fintype E]
  [DecidableEq E]
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {p : E × TripleMode}
-- given
  (hp : p ∈ tripleRealizedSchedule S base) :
-- imply
  (realizedList S.leftOrder base).idxOf p.1 = (tripleRealizedSchedule S base).idxOf p := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.idxOf_fst_tripleRealizedSchedule S base p hp

/--
[tripleScheduleProduct_eq_static](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleScheduleProduct_eq_static_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left right : ConfigSpace E}
  {schedule : List (E × TripleMode)}
-- given
  (hnd : (schedule.map Prod.fst).Nodup) :
-- imply
  tripleScheduleProduct μ F base left right schedule = staticTripleScheduleProduct μ F base left right schedule := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleScheduleProduct_eq_static μ F base left right schedule hnd

/--
[tripleJointProb_eq_tripleScheduleProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleJointProb_eq_tripleScheduleProduct_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left right : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R} :
-- imply
  tripleJointProb μ F base left right S = tripleScheduleProduct μ F base left right (tripleRealizedSchedule S base) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleJointProb_eq_tripleScheduleProduct μ F base left right S

/--
[staticTripleScheduleProduct_eq_prod_realized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma staticTripleScheduleProduct_eq_prod_realized_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E} :
-- imply
  staticTripleScheduleProduct μ ∅ base left right (tripleRealizedSchedule S base) = ∏ i : Fin (Fintype.card E), tripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i)) (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i) (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i) (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i) (base (realizedEquiv S.leftOrder base i)) (left (realizedEquiv S.leftOrder base i)) (right (realizedEquiv S.leftOrder base i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.staticTripleScheduleProduct_eq_prod_realized μ S base left right

/--
[flipTripleProb_beforeOfCausal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma flipTripleProb_beforeOfCausal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left right : ConfigSpace E}
  {z : E}
  {R : Finset E}
  {S : CausalOrder R} :
-- imply
  flipTripleProb μ F base left right z (TripleOrder.beforeOfCausal S) = 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipTripleProb_beforeOfCausal μ F base left right z S

/--
[flipCrossTripleProb_beforeOfCausal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma flipCrossTripleProb_beforeOfCausal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left right : ConfigSpace E}
  {z : E}
  {R : Finset E}
  {S : CausalOrder R} :
-- imply
  flipCrossTripleProb μ F base left right z (TripleOrder.beforeOfCausal S) = 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipCrossTripleProb_beforeOfCausal μ F base left right z S

/--
[flipBaseProb_beforeOfCausal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma flipBaseProb_beforeOfCausal_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base : ConfigSpace E}
  {z : E}
  {R : Finset E}
  {S : CausalOrder R} :
-- imply
  flipBaseProb μ F base z (TripleOrder.beforeOfCausal S) = 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipBaseProb_beforeOfCausal μ F base z S

/--
[flipTripleProb_extendDecisionTreeTriple_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma flipTripleProb_extendDecisionTreeTriple_none_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {T : DecisionTree E}
  {known base left right : ConfigSpace E}
  {R : Finset E}
  {z : E} :
-- imply
  flipTripleProb μ F base left right z (extendDecisionTreeTriple none T known R) = 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipTripleProb_extendDecisionTreeTriple_none μ F T known base left right R z

/--
[flipCrossTripleProb_extendDecisionTreeTriple_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma flipCrossTripleProb_extendDecisionTreeTriple_none_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {T : DecisionTree E}
  {known base left right : ConfigSpace E}
  {R : Finset E}
  {z : E} :
-- imply
  flipCrossTripleProb μ F base left right z (extendDecisionTreeTriple none T known R) = 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipCrossTripleProb_extendDecisionTreeTriple_none μ F T known base left right R z

/--
[flipBaseProb_extendDecisionTreeTriple_none](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma flipBaseProb_extendDecisionTreeTriple_none_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {T : DecisionTree E}
  {known base : ConfigSpace E}
  {R : Finset E}
  {z : E} :
-- imply
  flipBaseProb μ F base z (extendDecisionTreeTriple none T known R) = 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipBaseProb_extendDecisionTreeTriple_none μ F T known base R z

/--
[crossScheduleProduct_eq_static](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma crossScheduleProduct_eq_static_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left right : ConfigSpace E}
  {schedule : List (E × TripleMode)}
-- given
  (hnd : (schedule.map Prod.fst).Nodup) :
-- imply
  crossScheduleProduct μ F base left right schedule = staticCrossScheduleProduct μ F base left right schedule := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.crossScheduleProduct_eq_static μ F base left right schedule hnd

/--
[crossTripleJointProb_eq_crossScheduleProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma crossTripleJointProb_eq_crossScheduleProduct_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left right : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R} :
-- imply
  crossTripleJointProb μ F base left right S = crossScheduleProduct μ F base left right (tripleRealizedSchedule S base) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.crossTripleJointProb_eq_crossScheduleProduct μ F base left right S

/--
[staticCrossScheduleProduct_eq_prod_realized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma staticCrossScheduleProduct_eq_prod_realized_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E} :
-- imply
  staticCrossScheduleProduct μ ∅ base left right (tripleRealizedSchedule S base) = ∏ i : Fin (Fintype.card E), crossTripleWeight (tripleModeAt S base (realizedEquiv S.leftOrder base i)) (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) base i) (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) left i) (thr μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) right i) (base (realizedEquiv S.leftOrder base i)) (left (realizedEquiv S.leftOrder base i)) (right (realizedEquiv S.leftOrder base i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.staticCrossScheduleProduct_eq_prod_realized μ S base left right

/--
[tripleLabelCube_frozenCrossRawAtom_toReal_eq_crossTripleJointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleLabelCube_frozenCrossRawAtom_toReal_eq_crossTripleJointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  (tripleLabelCube (Fintype.card E) (frozenCrossRawAtom μ S base left right)).toReal = crossTripleJointProb μ ∅ base left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleLabelCube_frozenCrossRawAtom_toReal_eq_crossTripleJointProb μ hpos S base left right

/--
[tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  (tripleCube (Fintype.card E) (frozenCrossCodeAtom μ S base left right)).toReal = crossTripleJointProb μ ∅ base left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCube_frozenCrossCodeAtom_toReal_eq_crossTripleJointProb μ hpos S base left right

/--
[jointProb_allIndependent_eq_mul_pathProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma jointProb_allIndependent_eq_mul_pathProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base target : ConfigSpace E}
  {R : Finset E}
  {S : CausalOrder R} :
-- imply
  jointProb μ F base target (allIndependent S) = pathProb μ F base base S * pathProb μ F base target S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.jointProb_allIndependent_eq_mul_pathProb μ F base target S

/--
[realizedSchedule_map_fst](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realizedSchedule_map_fst_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E} :
-- imply
  (realizedSchedule S base).map Prod.fst = realizedList S base := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedSchedule_map_fst S base

/--
[realizedSchedule_length](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realizedSchedule_length_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E} :
-- imply
  (realizedSchedule S base).length = R.card := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedSchedule_length S base

/--
[realizedSchedule_mode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realizedSchedule_mode_eq
  [Fintype E]
  [DecidableEq E]
  {R : Finset E}
  {S : CausalOrder R}
  {base : ConfigSpace E}
  {p : E × Bool}
-- given
  (hp : p ∈ realizedSchedule S base) :
-- imply
  p.2 = independentAt S base p.1 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realizedSchedule_mode S base p hp

/--
[idxOf_fst_realizedSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma idxOf_fst_realizedSchedule_eq
  [Fintype E]
  [DecidableEq E]
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {p : E × Bool}
-- given
  (hp : p ∈ realizedSchedule S base) :
-- imply
  (realizedList S base).idxOf p.1 = (realizedSchedule S base).idxOf p := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.idxOf_fst_realizedSchedule S base p hp

/--
[scheduleProduct_eq_staticScheduleProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma scheduleProduct_eq_staticScheduleProduct_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base target : ConfigSpace E}
  {schedule : List (E × Bool)}
-- given
  (hnd : (schedule.map Prod.fst).Nodup) :
-- imply
  scheduleProduct μ F base target schedule = staticScheduleProduct μ F base target schedule := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.scheduleProduct_eq_staticScheduleProduct μ F base target schedule hnd

/--
[staticScheduleProduct_eq_prod_realized](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma staticScheduleProduct_eq_prod_realized_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : CausalOrder (Finset.univ : Finset E)}
  {base target : ConfigSpace E} :
-- imply
  staticScheduleProduct μ ∅ base target (realizedSchedule S base) = ∏ i : Fin (Fintype.card E), splitWeight (independentAt S base (realizedEquiv S base i)) (thr μ (realizedEquiv S base : Fin (Fintype.card E) → E) base i) (thr μ (realizedEquiv S base : Fin (Fintype.card E) → E) target i) (base (realizedEquiv S base i)) (target (realizedEquiv S base i)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.staticScheduleProduct_eq_prod_realized μ S base target

/--
[jointProb_eq_scheduleProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma jointProb_eq_scheduleProduct_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base target : ConfigSpace E}
  {R : Finset E}
  {S : CausalOrder R} :
-- imply
  jointProb μ F base target S = scheduleProduct μ F base target (realizedSchedule S base) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.jointProb_eq_scheduleProduct μ F base target S

/--
[pairedCube_frozenCodeAtom_toReal_eq_jointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_frozenCodeAtom_toReal_eq_jointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : CausalOrder (Finset.univ : Finset E)}
  {base target : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal = jointProb μ ∅ base target S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_frozenCodeAtom_toReal_eq_jointProb μ hpos S base target

/--
[pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  (pairedCube (Fintype.card E) (frozenTripleCodeAtom μ S base left right)).toReal = tripleJointProb μ ∅ base left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_frozenTripleCodeAtom_toReal_eq_tripleJointProb μ hpos S base left right

/--
[baseSum_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_split_eq
  [Fintype E]
  [DecidableEq E]
  {F : Finset E}
  {seed : ConfigSpace E}
  {H : ConfigSpace E → ℝ}
  {e : E}
-- given
  (he : e ∉ F) :
-- imply
  baseSum F seed H = baseSum (insert e F) (Function.update seed e false) H + baseSum (insert e F) (Function.update seed e true) H := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_split F seed H e he

/--
[baseSum_condMass_self_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_condMass_self_eq_one_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {seed : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  baseSum F seed (fun base => condMass μ F base base) = 1 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_condMass_self_eq_one μ hpos F seed

/--
[baseSum_tripleJointProb_eq_tripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_tripleJointProb_eq_tripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {seed left right : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun base => tripleJointProb μ F base left right S) = tripleProb μ F seed left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_tripleJointProb_eq_tripleProb μ F seed left right S hR

/--
[baseSum_flip_tripleJointProb_eq_flipTripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_flip_tripleJointProb_eq_flipTripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {seed left right : ConfigSpace E}
  {z : E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun base => (if tripleModeAt S base z = .flip then 1 else 0) * tripleJointProb μ F base left right S) = flipTripleProb μ F seed left right z S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_flip_tripleJointProb_eq_flipTripleProb μ F seed left right z S hR

/--
[baseSum_crossTripleJointProb_eq_crossTripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_crossTripleJointProb_eq_crossTripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {seed left right : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun base => crossTripleJointProb μ F base left right S) = crossTripleProb μ F seed left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_crossTripleJointProb_eq_crossTripleProb μ F seed left right S hR

/--
[baseSum_flip_crossTripleJointProb_eq_flipCrossTripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_flip_crossTripleJointProb_eq_flipCrossTripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {seed left right : ConfigSpace E}
  {z : E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun base => (if tripleModeAt S base z = .flip then 1 else 0) * crossTripleJointProb μ F base left right S) = flipCrossTripleProb μ F seed left right z S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_flip_crossTripleJointProb_eq_flipCrossTripleProb μ F seed left right z S hR

/--
[sum_tripleJointProb_empty_eq_tripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_tripleJointProb_empty_eq_tripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed left right : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)} :
-- imply
  ∑ base, tripleJointProb μ ∅ base left right S = tripleProb μ ∅ seed left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_tripleJointProb_empty_eq_tripleProb μ seed left right S

/--
[sum_pairedCube_frozenTripleCodeAtom_eq_tripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_pairedCube_frozenTripleCodeAtom_eq_tripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed left right : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ∑ base, (pairedCube (Fintype.card E) (frozenTripleCodeAtom μ S base left right)).toReal = tripleProb μ ∅ seed left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_pairedCube_frozenTripleCodeAtom_eq_tripleProb μ hpos seed left right S

/--
[sum_crossTripleJointProb_empty_eq_crossTripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_crossTripleJointProb_empty_eq_crossTripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed left right : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)} :
-- imply
  ∑ base, crossTripleJointProb μ ∅ base left right S = crossTripleProb μ ∅ seed left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_crossTripleJointProb_empty_eq_crossTripleProb μ seed left right S

/--
[sum_tripleCube_frozenCrossCodeAtom_eq_crossTripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_tripleCube_frozenCrossCodeAtom_eq_crossTripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed left right : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ∑ base, (tripleCube (Fintype.card E) (frozenCrossCodeAtom μ S base left right)).toReal = crossTripleProb μ ∅ seed left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_tripleCube_frozenCrossCodeAtom_eq_crossTripleProb μ hpos seed left right S

/--
[sum_frozenTripleCodeAtom_observable_eq_tripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_frozenTripleCodeAtom_observable_eq_tripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
  {g : ConfigSpace E → ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ∑ base, ∑ left, ∑ right, g left right * (pairedCube (Fintype.card E) (frozenTripleCodeAtom μ S base left right)).toReal = ∑ left, ∑ right, g left right * tripleProb μ ∅ seed left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_frozenTripleCodeAtom_observable_eq_tripleProb μ hpos seed S g

/--
[sum_frozenCrossCodeAtom_observable_eq_crossTripleProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_frozenCrossCodeAtom_observable_eq_crossTripleProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
  {g : ConfigSpace E → ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ∑ base, ∑ left, ∑ right, g left right * (tripleCube (Fintype.card E) (frozenCrossCodeAtom μ S base left right)).toReal = ∑ left, ∑ right, g left right * crossTripleProb μ ∅ seed left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_frozenCrossCodeAtom_observable_eq_crossTripleProb μ hpos seed S g

/--
[sum_frozenTripleCodeAtom_weighted_eq_tripleJointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_frozenTripleCodeAtom_weighted_eq_tripleJointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {g : ConfigSpace E → ConfigSpace E → ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ∑ base, ∑ left, ∑ right, g base left right * (pairedCube (Fintype.card E) (frozenTripleCodeAtom μ S base left right)).toReal = ∑ base, ∑ left, ∑ right, g base left right * tripleJointProb μ ∅ base left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_frozenTripleCodeAtom_weighted_eq_tripleJointProb μ hpos S g

/--
[sum_frozenCrossCodeAtom_weighted_eq_crossTripleJointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_frozenCrossCodeAtom_weighted_eq_crossTripleJointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {g : ConfigSpace E → ConfigSpace E → ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ∑ base, ∑ left, ∑ right, g base left right * (tripleCube (Fintype.card E) (frozenCrossCodeAtom μ S base left right)).toReal = ∑ base, ∑ left, ∑ right, g base left right * crossTripleJointProb μ ∅ base left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_frozenCrossCodeAtom_weighted_eq_crossTripleJointProb μ hpos S g

/--
[baseSum_jointProb_eq_targetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_jointProb_eq_targetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {seed target : ConfigSpace E}
  {R : Finset E}
  {S : CausalOrder R}
-- given
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun base => jointProb μ F base target S) = targetProb μ F seed target S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_jointProb_eq_targetProb μ F seed target S hR

/--
[sum_jointProb_empty_eq_targetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_jointProb_empty_eq_targetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed target : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)} :
-- imply
  ∑ base, jointProb μ ∅ base target S = targetProb μ ∅ seed target S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_jointProb_empty_eq_targetProb μ seed target S

/--
[baseSum_tripleJointProb_right_eq_jointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_tripleJointProb_right_eq_jointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left seed : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun right => tripleJointProb μ F base left right S) = jointProb μ F base left S.leftOrder := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_tripleJointProb_right_eq_jointProb μ hpos F base left seed S hR

/--
[baseSum_tripleJointProb_left_eq_jointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_tripleJointProb_left_eq_jointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base right seed : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun left => tripleJointProb μ F base left right S) = jointProb μ F base right S.rightOrder := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_tripleJointProb_left_eq_jointProb μ hpos F base right seed S hR

/--
[sum_tripleJointProb_right_eq_jointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_tripleJointProb_right_eq_jointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base left seed : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ∑ right, tripleJointProb μ ∅ base left right S = jointProb μ ∅ base left S.leftOrder := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_tripleJointProb_right_eq_jointProb μ hpos base left seed S

/--
[sum_tripleJointProb_left_eq_jointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_tripleJointProb_left_eq_jointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base right seed : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ∑ left, tripleJointProb μ ∅ base left right S = jointProb μ ∅ base right S.rightOrder := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_tripleJointProb_left_eq_jointProb μ hpos base right seed S

/--
[baseSum_tripleProb_right_eq_targetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_tripleProb_right_eq_targetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left seed : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun right => tripleProb μ F base left right S) = targetProb μ F base left S.leftOrder := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_tripleProb_right_eq_targetProb μ hpos F base left seed S hR

/--
[baseSum_tripleProb_left_eq_targetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_tripleProb_left_eq_targetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base right seed : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun left => tripleProb μ F base left right S) = targetProb μ F base right S.rightOrder := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_tripleProb_left_eq_targetProb μ hpos F base right seed S hR

/--
[baseSum_crossTripleProb_right_eq_targetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_crossTripleProb_right_eq_targetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base left seed : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun right => crossTripleProb μ F base left right S) = targetProb μ F base left S.leftOrder := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_crossTripleProb_right_eq_targetProb μ hpos F base left seed S hR

/--
[baseSum_crossTripleProb_left_eq_targetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_crossTripleProb_left_eq_targetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base right seed : ConfigSpace E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun left => crossTripleProb μ F base left right S) = targetProb μ F base right S.rightOrder := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_crossTripleProb_left_eq_targetProb μ hpos F base right seed S hR

/--
[jointProb_zero_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma jointProb_zero_support_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {F R : Finset E}
  {known base target : ConfigSpace E}
-- given
  (hR : R = Finset.univ \ F)
  (hknown : ∀ e, e ∉ R → known e = base e)
  (hagree : Agree F base target)
  (hnz : jointProb μ F base target (extendDecisionTreeAt 0 T known R) ≠ 0) :
-- imply
  T.eval base = T.eval target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.jointProb_zero_support μ T F R known base target hR hknown hagree hnz

/--
[jointProb_zero_support_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma jointProb_zero_support_univ_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {base target : ConfigSpace E}
-- given
  (hnz : jointProb μ ∅ base target (extendDecisionTreeAt 0 T base (Finset.univ : Finset E)) ≠ 0) :
-- imply
  T.eval base = T.eval target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.jointProb_zero_support_univ μ T base target hnz

/--
[targetIntegral_eq_targetProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma targetIntegral_eq_targetProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base target : ConfigSpace E}
  {R : Finset E}
  {S : CausalOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  targetIntegral μ F base target S = targetProb μ F base target S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.targetIntegral_eq_targetProb μ hpos F base target S

/--
[sum_pairedCube_frozenCodeAtom_eq_targetIntegral](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_pairedCube_frozenCodeAtom_eq_targetIntegral_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed target : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  ∑ base : ConfigSpace E, (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal = targetIntegral μ ∅ seed target S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_pairedCube_frozenCodeAtom_eq_targetIntegral μ hpos seed target S

/--
[condMass_chain_step](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma condMass_chain_step_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {target : ConfigSpace E}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (he : e ∉ F) :
-- imply
  condMass μ F target target = condProbBit μ F target e (target e) * condMass μ (insert e F) target target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.condMass_chain_step μ hpos F target e he

/--
[condProbBit_eq_closed_or_one_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma condProbBit_eq_closed_or_one_sub_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {target : ConfigSpace E}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  condProbBit μ F target e (target e) = if target e then 1 - condProbClosed μ F target e else condProbClosed μ F target e := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.condProbBit_eq_closed_or_one_sub μ hpos F target e

/--
[condObservable_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma condObservable_split_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {seed : ConfigSpace E}
  {g : ConfigSpace E → ℝ}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (he : e ∉ F) :
-- imply
  condObservable μ F seed g = bitWeight (condProbClosed μ F seed e) false * condObservable μ (insert e F) (Function.update seed e false) g + bitWeight (condProbClosed μ F seed e) true * condObservable μ (insert e F) (Function.update seed e true) g := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.condObservable_split μ hpos F seed g e he

/--
[condObservable_empty_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma condObservable_empty_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {g : ConfigSpace E → ℝ}
  {seed : ConfigSpace E}
-- given
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  condObservable μ ∅ seed g = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.condObservable_empty_eq_mean μ hμ1 g seed

/--
[baseSum_flip_condMass_eq_flipBaseProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma baseSum_flip_condMass_eq_flipBaseProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {seed : ConfigSpace E}
  {z : E}
  {R : Finset E}
  {S : TripleOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F seed (fun base => (if tripleModeAt S base z = .flip then 1 else 0) * condMass μ F base base) = flipBaseProb μ F seed z S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.baseSum_flip_condMass_eq_flipBaseProb μ hpos F seed z S hR

/--
[flipBaseProb_empty_eq_mean_flip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma flipBaseProb_empty_eq_mean_flip_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed : ConfigSpace E}
  {z : E}
  {S : TripleOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  flipBaseProb μ ∅ seed z S = Lindeberg.mean μ (fun base => if tripleModeAt S base z = .flip then 1 else 0) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipBaseProb_empty_eq_mean_flip μ hpos hμ1 seed z S

/--
[flipBaseProb_extendDecisionTreeTriple_eq_mean_sharedStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma flipBaseProb_extendDecisionTreeTriple_eq_mean_sharedStep_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {seed : ConfigSpace E}
  {t : ℕ}
  {z : E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  flipBaseProb μ ∅ seed z (extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E)) = Lindeberg.mean μ (fun base => sharedStepIndicator T base t z) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipBaseProb_extendDecisionTreeTriple_eq_mean_sharedStep μ hpos hμ1 T seed t z

/--
[targetProb_eq_condMass_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma targetProb_eq_condMass_core_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base target : ConfigSpace E}
  {R : Finset E}
  {S : CausalOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  targetProb μ F base target S = condMass μ F target target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.targetProb_eq_condMass_core μ hpos F base target S hR

/--
[flipTripleProb_right_marginal_extendDecisionTreeTriple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma flipTripleProb_right_marginal_extendDecisionTreeTriple_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {driver left rightSeed : ConfigSpace E}
  {z : E}
  {t : ℕ}
  {T : DecisionTree E}
  {known : ConfigSpace E}
  {R : Finset E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  baseSum F rightSeed (fun right => flipTripleProb μ F driver left right z (extendDecisionTreeTriple (some t) T known R)) = condMass μ F left left * flipBaseProb μ F driver z (extendDecisionTreeTriple (some t) T known R) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.flipTripleProb_right_marginal_extendDecisionTreeTriple μ hpos F driver left rightSeed z t T known R hR

/--
[pathProb_eq_condMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pathProb_eq_condMass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {driver target : ConfigSpace E}
  {R : Finset E}
  {S : CausalOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  pathProb μ F driver target S = condMass μ F target target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pathProb_eq_condMass μ hpos F driver target S hR

/--
[pathProb_empty_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pathProb_empty_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {driver target : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  pathProb μ ∅ driver target S = μ target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pathProb_empty_eq_mass μ hpos hμ1 driver target S

/--
[jointProb_allIndependent_empty_eq_mul_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma jointProb_allIndependent_empty_eq_mul_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base target : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  jointProb μ ∅ base target (allIndependent S) = μ base * μ target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.jointProb_allIndependent_empty_eq_mul_mass μ hpos hμ1 base target S

/--
[jointProb_extendDecisionTreeAt_card_eq_mul_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma jointProb_extendDecisionTreeAt_card_eq_mul_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {base target : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  jointProb μ ∅ base target (extendDecisionTreeAt (Fintype.card E) T base (Finset.univ : Finset E)) = μ base * μ target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.jointProb_extendDecisionTreeAt_card_eq_mul_mass μ hpos hμ1 T base target

/--
[causalPairEnergy_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalPairEnergy_zero_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E} :
-- imply
  causalPairEnergy μ T 0 = 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalPairEnergy_zero μ T

/--
[causalPairEnergy_card_eq_two_var](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalPairEnergy_card_eq_two_var_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  causalPairEnergy μ T (Fintype.card E) = 2 * Lindeberg.var μ T.evalR := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalPairEnergy_card_eq_two_var μ hpos hμ1 T

/--
[causalPairEnergy_succ_sub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalPairEnergy_succ_sub_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t = ∑ base, ∑ left, ∑ right, ((T.evalR base - T.evalR right) ^ 2 - (T.evalR base - T.evalR left) ^ 2) * tripleJointProb μ ∅ base left right (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalPairEnergy_succ_sub μ hpos T t

/--
[evalR_sqdiff_sub_sqdiff_le_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma evalR_sqdiff_sub_sqdiff_le_abs_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {base left right : ConfigSpace E} :
-- imply
  (T.evalR base - T.evalR right) ^ 2 - (T.evalR base - T.evalR left) ^ 2 ≤ |T.evalR right - T.evalR left| := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.evalR_sqdiff_sub_sqdiff_le_abs T base left right

/--
[tripleJointProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleJointProb_nonneg_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base left right : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  0 ≤ tripleJointProb μ ∅ base left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleJointProb_nonneg μ hpos S base left right

/--
[causalPairEnergy_succ_sub_le_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalPairEnergy_succ_sub_le_abs_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t ≤ ∑ base, ∑ left, ∑ right, |T.evalR right - T.evalR left| * tripleJointProb μ ∅ base left right (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalPairEnergy_succ_sub_le_abs μ hpos T t

/--
[tree_osss_of_causal_step_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tree_osss_of_causal_step_bound_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hStep : ∀ t < Fintype.card E, causalAbsJump μ T t ≤ 2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) * Lindeberg.mean μ (fun base => sharedStepIndicator T base t e)) :
-- imply
  Lindeberg.var μ T.evalR ≤ ∑ e, LindebergTree.revealmentMu μ T e * Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tree_osss_of_causal_step_bound μ hpos hμ1 T hStep

/--
[tripleJoint_left_energy_eq_causalPairEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleJoint_left_energy_eq_causalPairEnergy_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
  {seed : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E) ∑ base, ∑ left, ∑ right, (T.evalR base - T.evalR left) ^ 2 * tripleJointProb μ ∅ base left right S = causalPairEnergy μ T t := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleJoint_left_energy_eq_causalPairEnergy μ hpos T t seed

/--
[tripleJoint_right_energy_eq_causalPairEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleJoint_right_energy_eq_causalPairEnergy_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
  {seed : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E) ∑ base, ∑ left, ∑ right, (T.evalR base - T.evalR right) ^ 2 * tripleJointProb μ ∅ base left right S = causalPairEnergy μ T (t + 1) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleJoint_right_energy_eq_causalPairEnergy μ hpos T t seed

/--
[evalR_pair_energy_diff_le_abs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma evalR_pair_energy_diff_le_abs_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {base left right : ConfigSpace E} :
-- imply
  (T.evalR base - T.evalR right) ^ 2 - (T.evalR base - T.evalR left) ^ 2 ≤ |T.evalR right - T.evalR left| := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.evalR_pair_energy_diff_le_abs T base left right

/--
[abs_evalR_sub_eq_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma abs_evalR_sub_eq_disagreement_eq
  [Fintype E]
  [DecidableEq E]
  {T : DecisionTree E}
  {left right : ConfigSpace E} :
-- imply
  |T.evalR right - T.evalR left| = T.evalR right + T.evalR left - 2 * T.evalR right * T.evalR left := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.abs_evalR_sub_eq_disagreement T left right

/--
[causalTripleJump_eq_disagreement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalTripleJump_eq_disagreement_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
  {seed : ConfigSpace E} :
-- imply
  causalTripleJump μ T t seed = let S := extendDecisionTreeTriple (some t) T seed (Finset.univ : Finset E) ∑ base, ∑ left, ∑ right, (T.evalR right + T.evalR left - 2 * T.evalR right * T.evalR left) * tripleJointProb μ ∅ base left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalTripleJump_eq_disagreement μ T t seed

/--
[causalPairEnergy_sub_le_causalTripleJump](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causalPairEnergy_sub_le_causalTripleJump_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
  {seed : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  causalPairEnergy μ T (t + 1) - causalPairEnergy μ T t ≤ causalTripleJump μ T t seed := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causalPairEnergy_sub_le_causalTripleJump μ hpos T t seed

/--
[two_var_le_sum_causalTripleJump](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma two_var_le_sum_causalTripleJump_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {seed : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  2 * Lindeberg.var μ T.evalR ≤ ∑ t ∈ Finset.range (Fintype.card E), causalTripleJump μ T t seed := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.two_var_le_sum_causalTripleJump μ hpos hμ1 T seed

/--
[adaptive_tree_osss_of_causalTripleJump_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma adaptive_tree_osss_of_causalTripleJump_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {seed : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1)
  (hjump : ∀ t < Fintype.card E, causalTripleJump μ T t seed ≤ 2 * ∑ e, Lindeberg.cov μ T.evalR (Lindeberg.coord e) * Lindeberg.mean μ (fun base => sharedStepIndicator T base t e)) :
-- imply
  Lindeberg.var μ T.evalR ≤ ∑ e, LindebergTree.revealmentMu μ T e * Lindeberg.cov μ T.evalR (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.adaptive_tree_osss_of_causalTripleJump_le μ hpos hμ1 T seed hjump

/--
[targetProb_eq_condMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma targetProb_eq_condMass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {F : Finset E}
  {base target : ConfigSpace E}
  {R : Finset E}
  {S : CausalOrder R}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hR : R = Finset.univ \ F) :
-- imply
  targetProb μ F base target S = condMass μ F target target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.targetProb_eq_condMass μ hpos F base target S hR

/--
[targetProb_empty_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma targetProb_empty_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base target : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  targetProb μ ∅ base target S = μ target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.targetProb_empty_eq_mass μ hpos hμ1 base target S

/--
[sum_tripleProb_right_empty_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_tripleProb_right_empty_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base left seed : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ right, tripleProb μ ∅ base left right S = μ left := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_tripleProb_right_empty_eq_mass μ hpos hμ1 base left seed S

/--
[sum_tripleProb_left_empty_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_tripleProb_left_empty_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base right seed : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ left, tripleProb μ ∅ base left right S = μ right := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_tripleProb_left_empty_eq_mass μ hpos hμ1 base right seed S

/--
[sum_crossTripleProb_right_empty_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_crossTripleProb_right_empty_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base left seed : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ right, crossTripleProb μ ∅ base left right S = μ left := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_crossTripleProb_right_empty_eq_mass μ hpos hμ1 base left seed S

/--
[sum_crossTripleProb_left_empty_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_crossTripleProb_left_empty_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base right seed : ConfigSpace E}
  {S : TripleOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ left, crossTripleProb μ ∅ base left right S = μ right := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_crossTripleProb_left_empty_eq_mass μ hpos hμ1 base right seed S

/--
[sum_jointProb_empty_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_jointProb_empty_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed target : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ base, jointProb μ ∅ base target S = μ target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_jointProb_empty_eq_mass μ hpos hμ1 seed target S

/--
[sum_frozenCodeAtom_mass_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_frozenCodeAtom_mass_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed target : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ base, (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal = μ target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_frozenCodeAtom_mass_eq_mass μ hpos hμ1 seed target S

/--
[sum_frozenCodeAtom_observable_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_frozenCodeAtom_observable_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {seed : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ base, ∑ target, g target * (pairedCube (Fintype.card E) (frozenCodeAtom μ S base target)).toReal = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_frozenCodeAtom_observable_eq_mean μ hpos hμ1 seed S g

/--
[sum_targetProb_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_targetProb_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ target, g target * targetProb μ ∅ base target S = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_targetProb_eq_mean μ hpos hμ1 base S g

/--
[targetIntegral_empty_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma targetIntegral_empty_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base target : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  targetIntegral μ ∅ base target S = μ target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.targetIntegral_empty_eq_mass μ hpos hμ1 base target S

/--
[sum_diag_targetIntegral_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma sum_diag_targetIntegral_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {base : ConfigSpace E}
  {S : CausalOrder (Finset.univ : Finset E)}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ target, g target * targetIntegral μ ∅ base target S = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.sum_diag_targetIntegral_eq_mean μ hpos hμ1 base S g

/--
[decisionTree_mixed_targetIntegral_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma decisionTree_mixed_targetIntegral_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {base target : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  targetIntegral μ ∅ base target (extendDecisionTree T base (Finset.univ : Finset E)) = μ target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.decisionTree_mixed_targetIntegral_eq_mass μ hpos hμ1 T base target

/--
[decisionTree_mixed_diag_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma decisionTree_mixed_diag_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ target, g target * targetIntegral μ ∅ base target (extendDecisionTree T base (Finset.univ : Finset E)) = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.decisionTree_mixed_diag_eq_mean μ hpos hμ1 T base g

/--
[decisionTreeAt_mixed_targetIntegral_eq_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma decisionTreeAt_mixed_targetIntegral_eq_mass_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {t : ℕ}
  {T : DecisionTree E}
  {base target : ConfigSpace E}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  targetIntegral μ ∅ base target (extendDecisionTreeAt t T base (Finset.univ : Finset E)) = μ target := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.decisionTreeAt_mixed_targetIntegral_eq_mass μ hpos hμ1 t T base target

/--
[decisionTreeAt_mixed_diag_eq_mean](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma decisionTreeAt_mixed_diag_eq_mean_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {t : ℕ}
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hμ1 : ∑ ω, μ ω = 1) :
-- imply
  ∑ target, g target * targetIntegral μ ∅ base target (extendDecisionTreeAt t T base (Finset.univ : Finset E)) = Lindeberg.mean μ g := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.decisionTreeAt_mixed_diag_eq_mean μ hpos hμ1 t T base g

/--
[integral_eq_sum_fibre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma integral_eq_sum_fibre_eq
  [Fintype E]
  [DecidableEq E]
  [MeasurableSpace α]
  [Fintype β]
  [MeasurableSpace β]
  [MeasurableSingletonClass β]
  {ν : Measure α}
  [IsFiniteMeasure ν]
  {φ : α → β}
  {g : β → ℝ}
-- given
  (hφ : Measurable φ) :
-- imply
  (∫ x, g (φ x) ∂ν) = ∑ y, g y * (ν {x | φ x = y}).toReal := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.integral_eq_sum_fibre ν φ hφ g

/--
[pairedCube_causal_integral_eq_atom_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_causal_integral_eq_atom_sum_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {g : ConfigSpace E → ConfigSpace E → ℝ} :
-- imply
  (∫ z, (if (pairedCausalOutputs mu S base z).1 = base then g (pairedCausalOutputs mu S base z).2.1 (pairedCausalOutputs mu S base z).2.2 else 0) ∂(pairedCube (Fintype.card E))) = ∑ left, ∑ right, g left right * (pairedCube (Fintype.card E) (frozenTripleCodeAtom mu S base left right)).toReal := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_causal_integral_eq_atom_sum mu S base g

/--
[pairedCube_causal_integral_eq_tripleJointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_causal_integral_eq_tripleJointProb_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {g : ConfigSpace E → ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < mu ω) :
-- imply
  (∫ z, (if (pairedCausalOutputs mu S base z).1 = base then g (pairedCausalOutputs mu S base z).2.1 (pairedCausalOutputs mu S base z).2.2 else 0) ∂(pairedCube (Fintype.card E))) = ∑ left, ∑ right, g left right * tripleJointProb mu ∅ base left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_causal_integral_eq_tripleJointProb mu hpos S base g

/--
[tripleCube_causal_integral_eq_atom_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCube_causal_integral_eq_atom_sum_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {g : ConfigSpace E → ConfigSpace E → ℝ} :
-- imply
  (∫ z, (if (tripleCausalOutputs μ S base z).1 = base then g (tripleCausalOutputs μ S base z).2.1 (tripleCausalOutputs μ S base z).2.2 else 0) ∂(tripleCube (Fintype.card E))) = ∑ left, ∑ right, g left right * (tripleCube (Fintype.card E) (frozenCrossCodeAtom μ S base left right)).toReal := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCube_causal_integral_eq_atom_sum μ S base g

/--
[tripleCube_causal_integral_eq_crossTripleJointProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCube_causal_integral_eq_crossTripleJointProb_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {g : ConfigSpace E → ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω) :
-- imply
  (∫ z, (if (tripleCausalOutputs μ S base z).1 = base then g (tripleCausalOutputs μ S base z).2.1 (tripleCausalOutputs μ S base z).2.2 else 0) ∂(tripleCube (Fintype.card E))) = ∑ left, ∑ right, g left right * crossTripleJointProb μ ∅ base left right S := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCube_causal_integral_eq_crossTripleJointProb μ hpos S base g

/--
[pairedCube_causal_integral_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma pairedCube_causal_integral_pullback_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {g : ConfigSpace E → ConfigSpace E → ℝ} :
-- imply
  (∫ z, (if (pairedCausalOutputs mu S base z).1 = base then g (pairedCausalOutputs mu S base z).2.1 (pairedCausalOutputs mu S base z).2.2 else 0) ∂(pairedCube (Fintype.card E))) = ∫ p, (if codeMap mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) p.1 = base then g (codeMap mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) (causalMixLabels S.leftOrder base p.1 p.2)) (codeMap mu (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) (causalMixLabels S.rightOrder base p.1 p.2)) else 0) ∂((GrandCoupling.Vcube (Fintype.card E)).prod (GrandCoupling.Vcube (Fintype.card E))) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.pairedCube_causal_integral_pullback mu S base g

/--
[tripleCube_causal_integral_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCube_causal_integral_pullback_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {g : ConfigSpace E → ConfigSpace E → ℝ} :
-- imply
  (∫ z, (if (tripleCausalOutputs μ S base z).1 = base then g (tripleCausalOutputs μ S base z).2.1 (tripleCausalOutputs μ S base z).2.2 else 0) ∂(tripleCube (Fintype.card E))) = ∫ q, (if codeMap μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) q.1.1 = base then g (codeMap μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) (causalMixLabels S.leftOrder base q.1.1 q.1.2)) (codeMap μ (realizedEquiv S.leftOrder base : Fin (Fintype.card E) → E) (causalMixLabels S.rightOrder base q.1.1 q.2)) else 0) ∂(((GrandCoupling.Vcube (Fintype.card E)).prod (GrandCoupling.Vcube (Fintype.card E))).prod (GrandCoupling.Vcube (Fintype.card E))) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCube_causal_integral_pullback μ S base g

/--
[tripleCube_conditional_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCube_conditional_product_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {A : (Fin n → ℝ) → ℝ}
  {F G : (Fin n → ℝ) → (Fin n → ℝ) → ℝ}
  {CA CF CG : ℝ}
-- given
  (hAm : Measurable A)
  (hFm : Measurable (Function.uncurry F))
  (hGm : Measurable (Function.uncurry G))
  (hAC : ∀ U, |A U| ≤ CA)
  (hFC : ∀ U V, |F U V| ≤ CF)
  (hGC : ∀ U V, |G U V| ≤ CG) :
-- imply
  (∫ q, A q.1.1 * F q.1.1 q.1.2 * G q.1.1 q.2 ∂((GrandCoupling.Vcube n).prod (GrandCoupling.Vcube n)).prod (GrandCoupling.Vcube n)) = ∫ U, A U * (∫ V, F U V ∂(GrandCoupling.Vcube n)) * (∫ V, G U V ∂(GrandCoupling.Vcube n)) ∂(GrandCoupling.Vcube n) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCube_conditional_product A F G hAm hFm hGm hAC hFC hGC

/--
[tripleCube_product_le_pairedCube_product](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma tripleCube_product_le_pairedCube_product_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {g : ConfigSpace E → ℝ}
  {Cg : ℝ}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hmono : IsMonotonicMeasure mu)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf)
  (hg : Monotone g)
  (hgC : ∀ ω, |g ω| ≤ Cg) :
-- imply
  (∫ z, (if (tripleCausalOutputs mu S base z).1 = base then f (tripleCausalOutputs mu S base z).2.1 * g (tripleCausalOutputs mu S base z).2.2 else 0) ∂(tripleCube (Fintype.card E))) ≤ ∫ z, (if (pairedCausalOutputs mu S base z).1 = base then f (pairedCausalOutputs mu S base z).2.1 * g (pairedCausalOutputs mu S base z).2.2 else 0) ∂(pairedCube (Fintype.card E)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.tripleCube_product_le_pairedCube_product hpos hmono S base hf hfC hg hgC

/--
[no_flip_causal_atom_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma no_flip_causal_atom_eq_zero_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S : TripleOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {f : ConfigSpace E → ℝ}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hno : ∀ e, tripleModeAt S base e ≠ .flip) :
-- imply
  (∑ left, ∑ right, |f right - f left| * tripleJointProb mu ∅ base left right S) = 0 := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.no_flip_causal_atom_eq_zero mu hpos S base hno f

/--
[decisionTree_flip_atom_step_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma decisionTree_flip_atom_step_le_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {t : ℕ}
  {base : ConfigSpace E}
  {e : E}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hmono : IsMonotonicMeasure mu)
  (hf : Monotone T.evalR)
  (he : tripleModeAt (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e = .flip) :
-- imply
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E) (∑ left, ∑ right, |T.evalR right - T.evalR left| * tripleJointProb mu ∅ base left right S) ≤ (∑ left, ∑ right, (T.evalR left * Lindeberg.coord e left + T.evalR right * Lindeberg.coord e right) * tripleJointProb mu ∅ base left right S) - (∑ left, ∑ right, (T.evalR left * Lindeberg.coord e right + T.evalR right * Lindeberg.coord e left) * crossTripleJointProb mu ∅ base left right S) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.decisionTree_flip_atom_step_le mu hpos hmono T t hf base e he

/--
[causal_fkg_cross_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causal_fkg_cross_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {S₁ S₂ : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {σ : Fin (Fintype.card E) ≃ E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {e : E}
  {U : Fin (Fintype.card E) → ℝ}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hmono : IsMonotonicMeasure mu)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf) :
-- imply
  (∫ V, f (codeMap mu (σ : Fin (Fintype.card E) → E) (causalMixLabels S₁ base U V)) ∂(GrandCoupling.Vcube (Fintype.card E))) * (∫ V, Lindeberg.coord e (codeMap mu (σ : Fin (Fintype.card E) → E) (causalMixLabels S₂ base U V)) ∂(GrandCoupling.Vcube (Fintype.card E))) ≤ ∫ V, f (codeMap mu (σ : Fin (Fintype.card E) → E) (causalMixLabels S₁ base U V)) * Lindeberg.coord e (codeMap mu (σ : Fin (Fintype.card E) → E) (causalMixLabels S₂ base U V)) ∂(GrandCoupling.Vcube (Fintype.card E)) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causal_fkg_cross_fiber hpos hmono S₁ S₂ base σ hf hfC e U

/--
[causal_abs_integral_fiber_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma causal_abs_integral_fiber_le_eq
  [Fintype E]
  [DecidableEq E]
  {mu : ConfigSpace E → ℝ}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {t : ℕ}
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {e : E}
  {U : Fin (Fintype.card E) → ℝ}
-- given
  (hpos : ∀ ω, 0 < mu ω)
  (hmono : IsMonotonicMeasure mu)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf)
  (he : tripleModeAt (extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E)) base e = .flip) :
-- imply
  let S := extendDecisionTreeTriple (some t) T base (Finset.univ : Finset E) let σ := realizedEquiv S.leftOrder base let Yl := fun V => codeMap mu (σ : Fin (Fintype.card E) → E) (causalMixLabels S.leftOrder base U V) let Yr := fun V => codeMap mu (σ : Fin (Fintype.card E) → E) (causalMixLabels S.rightOrder base U V) (∫ V, |f (Yr V) - f (Yl V)| ∂(GrandCoupling.Vcube (Fintype.card E))) ≤ (∫ V, f (Yl V) * Lindeberg.coord e (Yl V) ∂(GrandCoupling.Vcube (Fintype.card E))) + (∫ V, f (Yr V) * Lindeberg.coord e (Yr V) ∂(GrandCoupling.Vcube (Fintype.card E))) - (∫ V, f (Yl V) ∂(GrandCoupling.Vcube (Fintype.card E))) * (∫ V, Lindeberg.coord e (Yr V) ∂(GrandCoupling.Vcube (Fintype.card E))) - (∫ V, f (Yr V) ∂(GrandCoupling.Vcube (Fintype.card E))) * (∫ V, Lindeberg.coord e (Yl V) ∂(GrandCoupling.Vcube (Fintype.card E))) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.causal_abs_integral_fiber_le hpos hmono hf hfC t T base e he U

/--
[realized_step_fiber_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma realized_step_fiber_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {S : CausalOrder (Finset.univ : Finset E)}
  {base : ConfigSpace E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {t : ℕ}
  {U : Fin (Fintype.card E) → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf)
  (ht : 1 ≤ t)
  (htn : t - 1 < Fintype.card E) :
-- imply
  fiberAbsStep μ (realizedEquiv S base) f U t ≤ fiberObservable μ (realizedEquiv S base) (fun ω => f ω * Lindeberg.coord ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩) ω) U (t - 1) + fiberObservable μ (realizedEquiv S base) (fun ω => f ω * Lindeberg.coord ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩) ω) U t - fiberObservable μ (realizedEquiv S base) f U (t - 1) * fiberObservable μ (realizedEquiv S base) (Lindeberg.coord ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩)) U t - fiberObservable μ (realizedEquiv S base) f U t * fiberObservable μ (realizedEquiv S base) (Lindeberg.coord ((realizedEquiv S base : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩)) U (t - 1) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.realized_step_fiber_le hpos hmono S base hf hfC t ht htn U

/--
[decisionTree_branch_adapt_step_fiber_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/AdaptiveCausalKernel.lean)
-/
@[path]
private lemma decisionTree_branch_adapt_step_fiber_le_eq
  [Fintype E]
  [DecidableEq E]
  {μ : ConfigSpace E → ℝ}
  {T : DecisionTree E}
  {base : ConfigSpace E}
  {f : ConfigSpace E → ℝ}
  {Cf : ℝ}
  {t : ℕ}
  {U : Fin (Fintype.card E) → ℝ}
-- given
  (hpos : ∀ ω, 0 < μ ω)
  (hmono : IsMonotonicMeasure μ)
  (hf : Monotone f)
  (hfC : ∀ ω, |f ω| ≤ Cf)
  (ht : 1 ≤ t)
  (htm : t ≤ (T.queried base).card)
  (htn : t - 1 < Fintype.card E) :
-- imply
  let S := extendDecisionTree T base (Finset.univ : Finset E) let σ := realizedEquiv S base let m := (T.queried base).card let e := (σ : Fin (Fintype.card E) → E) ⟨t - 1, htn⟩ fiberAdaptAbsStep μ σ f U m t ≤ fiberAdaptObservable μ σ (fun ω => f ω * Lindeberg.coord e ω) U m (t - 1) + fiberAdaptObservable μ σ (fun ω => f ω * Lindeberg.coord e ω) U m t - fiberAdaptObservable μ σ f U m (t - 1) * fiberAdaptObservable μ σ (Lindeberg.coord e) U m t - fiberAdaptObservable μ σ f U m t * fiberAdaptObservable μ σ (Lindeberg.coord e) U m (t - 1) := by
-- proof
  apply StatMech.OSSS.AdaptiveCausalKernel.decisionTree_branch_adapt_step_fiber_le hpos hmono T base hf hfC t ht htm htn U


-- created on 2026-10-23
