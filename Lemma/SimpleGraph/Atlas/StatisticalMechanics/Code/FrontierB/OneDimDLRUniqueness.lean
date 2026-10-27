import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part8
open Finset Matrix StatMech StatMech.FrontierB


/--
[pathCastEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma pathCastEquiv_apply_eq
  {E : Type*}
  {m n : ℕ}
  {q : Fin m → E}
  {i : Fin n}
-- given
  (h : m = n) :
-- imply
  pathCastEquiv E h q i = q (Fin.cast h.symm i) := by
-- proof
  apply StatMech.FrontierB.pathCastEquiv_apply E h q i

/--
[pathCastEquiv_symm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma pathCastEquiv_symm_apply_eq
  {E : Type*}
  {m n : ℕ}
  {q : Fin n → E}
  {i : Fin m}
-- given
  (h : m = n) :
-- imply
  (pathCastEquiv E h).symm q i = q (Fin.cast h i) := by
-- proof
  apply StatMech.FrontierB.pathCastEquiv_symm_apply E h q i

/--
[openMatrixProduct_pathCast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma openMatrixProduct_pathCast_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {a b : E}
  {m n : ℕ}
  {q : Fin m → E}
-- given
  (h : m = n) :
-- imply
  openMatrixProduct A a b (pathCastEquiv E h q) = openMatrixProduct A a b q := by
-- proof
  apply StatMech.FrontierB.openMatrixProduct_pathCast A a b h q

/--
[wordHeadSplitEquiv_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma wordHeadSplitEquiv_center_eq
  {E : Type*}
  {m k n : ℕ}
  {s : E}
  {l : Fin m → E}
  {r : Fin (n + k + 1) → E} :
-- imply
  wordHeadSplitEquiv E m k n (s, (l, r)) ⟨m, by omega⟩ = s := by
-- proof
  apply StatMech.FrontierB.wordHeadSplitEquiv_center E m k n s l r

/--
[wordHeadSplitEquiv_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma wordHeadSplitEquiv_right_eq
  {E : Type*}
  {m k n : ℕ}
  {s : E}
  {l : Fin m → E}
  {r : Fin (n + k + 1) → E}
  {i : Fin (n + k + 1)} :
-- imply
  wordHeadSplitEquiv E m k n (s, (l, r)) ⟨m + 1 + i.val, by omega⟩ = r i := by
-- proof
  apply StatMech.FrontierB.wordHeadSplitEquiv_right E m k n s l r i

/--
[openMatrixProduct_wordHeadSplit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma openMatrixProduct_wordHeadSplit_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {a s b : E}
  {m k n : ℕ}
  {l : Fin m → E}
  {r : Fin (n + k + 1) → E} :
-- imply
  openMatrixProduct A a b (wordHeadSplitEquiv E m k n (s, (l, r))) = openMatrixProduct A a s l * openMatrixProduct A s b r := by
-- proof
  apply StatMech.FrontierB.openMatrixProduct_wordHeadSplit A a s b m k n l r

/--
[pathContainsWord_succ_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma pathContainsWord_succ_split_eq
  {m k n : ℕ}
  {p : Fin (k + 2) → E}
  {s : E}
  {l : Fin m → E}
  {r : Fin (n + k + 1) → E} :
-- imply
  pathContainsWord p (wordHeadSplitEquiv E m k n (s, (l, r))) ↔ s = p 0 ∧ pathContainsWord (m := 0) (n := n) (Fin.tail p) ((pathCastEquiv E (by omega : 0 + (n + k) + 1 = n + k + 1)).symm r) := by
-- proof
  apply StatMech.FrontierB.pathContainsWord_succ_split m k n p s l r

/--
[pathContainsWord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma pathContainsWord_zero_eq
  {m n : ℕ}
  {p : Fin 1 → E}
  {q : Fin (m + (n + 0) + 1) → E} :
-- imply
  pathContainsWord p q ↔ q ⟨m, by omega⟩ = p 0 := by
-- proof
  apply StatMech.FrontierB.pathContainsWord_zero m n p q

/--
[fixedWordProduct_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma fixedWordProduct_tail_eq
  [CommMonoid R]
  {A : Matrix E E R}
  {k : ℕ}
  {p : Fin (k + 2) → E} :
-- imply
  fixedWordProduct A p = A (p 0) (p 1) * fixedWordProduct A (Fin.tail p) := by
-- proof
  apply StatMech.FrontierB.fixedWordProduct_tail A p

/--
[sum_openMatrixProduct_fixedWord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma sum_openMatrixProduct_fixedWord_eq
  [Fintype E]
  [DecidableEq E]
  [CommSemiring R]
  {A : Matrix E E R}
  {a b : E} :
-- imply
  ∀ (k m n : ℕ) (p : Fin (k + 1) → E), (∑ q : Fin (m + (n + k) + 1) → E, if pathContainsWord p q then openMatrixProduct A a b q else 0) = (A ^ (m + 1)) a (p 0) * fixedWordProduct A p * (A ^ (n + 1)) (p (Fin.last k)) b := by
-- proof
  apply StatMech.FrontierB.sum_openMatrixProduct_fixedWord A a b

/--
[measurableSet_blockStateEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma measurableSet_blockStateEvent_eq
  {r : ℕ}
  {p : Fin (2 * r + 1) → Fin 2} :
-- imply
  MeasurableSet (blockStateEvent r p) := by
-- proof
  apply StatMech.FrontierB.measurableSet_blockStateEvent r p

/--
[blockInteriorStateEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma blockInteriorStateEquiv_apply_eq
  {eta : ConfigSpace (Site 1)}
  {r m : ℕ}
  {i : Fin (2 * r + 1)}
-- given
  (tau : {x // x ∈ box 1 (r + m)} → Bool) :
-- imply
  blockInteriorStateEquiv r m tau ⟨m + i.val, by omega⟩ = boolTransferState (glue eta tau (site1 (-(r : ℤ) + (i.val : ℤ)))) := by
-- proof
  apply StatMech.FrontierB.blockInteriorStateEquiv_apply eta r m tau i

/--
[pathContainsWord_block_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma pathContainsWord_block_iff_eq
  {eta : ConfigSpace (Site 1)}
  {r m : ℕ}
  {p : Fin (2 * r + 1) → Fin 2}
-- given
  (tau : {x // x ∈ box 1 (r + m)} → Bool) :
-- imply
  pathContainsWord (m := m) (n := m) p (blockInteriorStateEquiv r m tau) ↔ glue eta tau ∈ blockStateEvent r p := by
-- proof
  apply StatMech.FrontierB.pathContainsWord_block_iff eta r m tau p

/--
[sum_fvTransferProduct_block_eq_matrix_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma sum_fvTransferProduct_block_eq_matrix_pow_eq
  {eta : ConfigSpace (Site 1)}
  {r m : ℕ}
  {p : Fin (2 * r + 1) → Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  (∑ tau : {x // x ∈ box 1 (r + m)} → Bool, if glue eta tau ∈ blockStateEvent r p then fvTransferProduct eta (r + m) tau beta h else 0) = (isingTransferReal beta (beta * h) ^ (m + 1)) (fvLeftBoundaryState eta (r + m)) (p 0) * fixedWordProduct (isingTransferReal beta (beta * h)) p * (isingTransferReal beta (beta * h) ^ (m + 1)) (p (Fin.last (2 * r))) (fvRightBoundaryState eta (r + m)) := by
-- proof
  apply StatMech.FrontierB.sum_fvTransferProduct_block_eq_matrix_pow eta r m beta h p

/--
[sum_fvWeight_block_eq_matrix_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma sum_fvWeight_block_eq_matrix_pow_eq
  {eta : ConfigSpace (Site 1)}
  {r m : ℕ}
  {p : Fin (2 * r + 1) → Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  (∑ tau : {x // x ∈ box 1 (r + m)} → Bool, if glue eta tau ∈ blockStateEvent r p then fvWeight eta (r + m) (bondFinsetTouch 1 (r + m)) beta h tau else 0) = fvEndpointFactor eta (r + m) beta h * ((isingTransferReal beta (beta * h) ^ (m + 1)) (fvLeftBoundaryState eta (r + m)) (p 0) * fixedWordProduct (isingTransferReal beta (beta * h)) p * (isingTransferReal beta (beta * h) ^ (m + 1)) (p (Fin.last (2 * r))) (fvRightBoundaryState eta (r + m))) := by
-- proof
  apply StatMech.FrontierB.sum_fvWeight_block_eq_matrix_pow eta r m beta h p

/--
[fvBlockStateProb_eq_matrix_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma fvBlockStateProb_eq_matrix_ratio_eq
  {eta : ConfigSpace (Site 1)}
  {r m : ℕ}
  {p : Fin (2 * r + 1) → Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  fvBlockStateProb eta r m beta h p = ((isingTransferReal beta (beta * h) ^ (m + 1)) (fvLeftBoundaryState eta (r + m)) (p 0) * fixedWordProduct (isingTransferReal beta (beta * h)) p * (isingTransferReal beta (beta * h) ^ (m + 1)) (p (Fin.last (2 * r))) (fvRightBoundaryState eta (r + m))) / (isingTransferReal beta (beta * h) ^ (2 * (r + m) + 2)) (fvLeftBoundaryState eta (r + m)) (fvRightBoundaryState eta (r + m)) := by
-- proof
  apply StatMech.FrontierB.fvBlockStateProb_eq_matrix_ratio eta r m beta h p

/--
[fvMeasure_blockStateEvent_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma fvMeasure_blockStateEvent_real_eq
  {eta : ConfigSpace (Site 1)}
  {r m : ℕ}
  {p : Fin (2 * r + 1) → Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  (fvMeasure eta (r + m) (bondFinsetTouch 1 (r + m)) beta h).real (blockStateEvent r p) = fvBlockStateProb eta r m beta h p := by
-- proof
  apply StatMech.FrontierB.fvMeasure_blockStateEvent_real eta r m beta h p

/--
[isingTransferProjectorPlus_cross_general](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma isingTransferProjectorPlus_cross_general_eq
  {a c d b : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  isingTransferProjectorPlus beta h a c * isingTransferProjectorPlus beta h d b = isingTransferProjectorPlus beta h a b * isingTransferProjectorPlus beta h d c := by
-- proof
  apply StatMech.FrontierB.isingTransferProjectorPlus_cross_general beta h a c d b

/--
[isingTransfer_fixedWord_weight_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma isingTransfer_fixedWord_weight_tendsto_eq
  {k : ℕ}
  {p : Fin (k + 1) → Fin 2}
  {a b : Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun m : ℕ => (isingTransferReal beta h ^ (m + 1)) a (p 0) * fixedWordProduct (isingTransferReal beta h) p * (isingTransferReal beta h ^ (m + 1)) (p (Fin.last k)) b / (isingTransferReal beta h ^ (2 * (m + 1) + k)) a b) Filter.atTop (nhds (isingTransferProjectorPlus beta h (p (Fin.last k)) (p 0) * fixedWordProduct (isingTransferReal beta h) p * (isingTransferEigenPlus beta h)⁻¹ ^ k)) := by
-- proof
  apply StatMech.FrontierB.isingTransfer_fixedWord_weight_tendsto beta h k p a b

/--
[fvBlockStateProb_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma fvBlockStateProb_tendsto_eq
  {eta : ℕ → ConfigSpace (Site 1)}
  {r : ℕ}
  {p : Fin (2 * r + 1) → Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun m => fvBlockStateProb (eta m) r m beta h p) Filter.atTop (nhds (blockStateLimit r beta h p)) := by
-- proof
  apply StatMech.FrontierB.fvBlockStateProb_tendsto eta r beta h p

/--
[fvMeasure_blockStateEvent_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma fvMeasure_blockStateEvent_tendsto_eq
  {eta : ℕ → ConfigSpace (Site 1)}
  {r : ℕ}
  {p : Fin (2 * r + 1) → Fin 2}
-- given
  (beta h : ℝ) :
-- imply
  Filter.Tendsto (fun m => (fvMeasure (eta m) (r + m) (bondFinsetTouch 1 (r + m)) beta h).real (blockStateEvent r p)) Filter.atTop (nhds (blockStateLimit r beta h p)) := by
-- proof
  apply StatMech.FrontierB.fvMeasure_blockStateEvent_tendsto eta r beta h p

/--
[dlr_blockStateEvent_real_eq_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma dlr_blockStateEvent_real_eq_limit_eq
  {mu : Measure (ConfigSpace (Site 1))}
  [IsProbabilityMeasure mu]
  {r : ℕ}
  {p : Fin (2 * r + 1) → Fin 2}
-- given
  (beta h : ℝ)
  (hmu : IsDLRState 1 beta h mu) :
-- imply
  mu.real (blockStateEvent r p) = blockStateLimit r beta h p := by
-- proof
  apply StatMech.FrontierB.dlr_blockStateEvent_real_eq_limit beta h mu hmu r p

/--
[measurable_intervalStatePattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma measurable_intervalStatePattern_eq
  {r : ℕ} :
-- imply
  Measurable (intervalStatePattern r) := by
-- proof
  apply StatMech.FrontierB.measurable_intervalStatePattern r

/--
[intervalStatePattern_preimage_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma intervalStatePattern_preimage_singleton_eq
  {r : ℕ}
  {p : Fin (2 * r + 1) → Fin 2} :
-- imply
  intervalStatePattern r ⁻¹' {p} = blockStateEvent r p := by
-- proof
  apply StatMech.FrontierB.intervalStatePattern_preimage_singleton r p

/--
[map_intervalStatePattern_eq_of_block_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma map_intervalStatePattern_eq_of_block_eq_eq
  {mu nu : Measure (ConfigSpace (Site 1))}
  [IsFiniteMeasure mu]
  [IsFiniteMeasure nu]
  {r : ℕ}
-- given
  (hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2), mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p)) :
-- imply
  Measure.map (intervalStatePattern r) mu = Measure.map (intervalStatePattern r) nu := by
-- proof
  apply StatMech.FrontierB.map_intervalStatePattern_eq_of_block_eq hblock r

/--
[intervalPatternRestriction_pattern](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma intervalPatternRestriction_pattern_eq
  {r : ℕ}
  {t : Finset (Site 1)}
  {sigma : ConfigSpace (Site 1)}
-- given
  (ht : (t : Set (Site 1)) ⊆ box 1 r) :
-- imply
  intervalPatternRestriction r t ht (intervalStatePattern r sigma) = fun x : t => sigma x.1 := by
-- proof
  apply StatMech.FrontierB.intervalPatternRestriction_pattern r t ht sigma

/--
[map_finsetRestriction_eq_of_block_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma map_finsetRestriction_eq_of_block_eq_eq
  {mu nu : Measure (ConfigSpace (Site 1))}
  [IsFiniteMeasure mu]
  [IsFiniteMeasure nu]
  {t : Finset (Site 1)}
-- given
  (hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2), mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p)) :
-- imply
  Measure.map (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) mu = Measure.map (fun sigma : ConfigSpace (Site 1) => fun x : t => sigma x.1) nu := by
-- proof
  apply StatMech.FrontierB.map_finsetRestriction_eq_of_block_eq hblock t

/--
[measure_cylinder_eq_of_block_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma measure_cylinder_eq_of_block_eq_eq
  {mu nu : Measure (ConfigSpace (Site 1))}
  [IsFiniteMeasure mu]
  [IsFiniteMeasure nu]
  {t : Finset (Site 1)}
  {S : Set (t → Bool)}
-- given
  (hblock : ∀ (r : ℕ) (p : Fin (2 * r + 1) → Fin 2), mu.real (blockStateEvent r p) = nu.real (blockStateEvent r p))
  (hS : MeasurableSet S) :
-- imply
  mu (cylinder t S) = nu (cylinder t S) := by
-- proof
  apply StatMech.FrontierB.measure_cylinder_eq_of_block_eq hblock t S hS

/--
[oneDim_isDLRState_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean)
-/
@[path]
private lemma oneDim_isDLRState_unique_eq
  {mu nu : Measure (ConfigSpace (Site 1))}
  [IsProbabilityMeasure mu]
  [IsProbabilityMeasure nu]
-- given
  (beta h : ℝ)
  (hmu : IsDLRState 1 beta h mu)
  (hnu : IsDLRState 1 beta h nu) :
-- imply
  mu = nu := by
-- proof
  apply StatMech.FrontierB.oneDim_isDLRState_unique beta h mu nu hmu hnu


-- created on 2026-10-23
