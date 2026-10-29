import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductApprox.Part6
open MeasureTheory Set Filter Topology StatMech StatMech.FrontierA


/--
[IsFiniteCoordinateSet.measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma measurableSet_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {A : Set (∀ e, S e)}
-- given
  (hA : IsFiniteCoordinateSet A) :
-- imply
  MeasurableSet A := by
-- proof
  apply StatMech.FrontierA.IsFiniteCoordinateSet.measurableSet hA

/--
[isFiniteCoordinateSet_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma isFiniteCoordinateSet_empty_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E] :
-- imply
  IsFiniteCoordinateSet (∅ : Set (∀ e, S e)) := by
-- proof
  apply StatMech.FrontierA.isFiniteCoordinateSet_empty

/--
[IsFiniteCoordinateSet.union](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma union_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {A B : Set (∀ e, S e)}
-- given
  (hA : IsFiniteCoordinateSet A)
  (hB : IsFiniteCoordinateSet B) :
-- imply
  IsFiniteCoordinateSet (A ∪ B) := by
-- proof
  apply StatMech.FrontierA.IsFiniteCoordinateSet.union hA hB

/--
[IsFiniteCoordinateSet.diff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma diff_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {A B : Set (∀ e, S e)}
-- given
  (hA : IsFiniteCoordinateSet A)
  (hB : IsFiniteCoordinateSet B) :
-- imply
  IsFiniteCoordinateSet (A \ B) := by
-- proof
  apply StatMech.FrontierA.IsFiniteCoordinateSet.diff hA hB

/--
[isSetRing_isFiniteCoordinateSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma isSetRing_isFiniteCoordinateSet_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E] :
-- imply
  IsSetRing {A : Set (∀ e, S e) | IsFiniteCoordinateSet A} where empty_mem := by
-- proof
  apply StatMech.FrontierA.isSetRing_isFiniteCoordinateSet

/--
[rectangle_isFiniteCoordinateSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma rectangle_isFiniteCoordinateSet_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
-- given
  (s : ∀ e, Set (S e))
  (hs : ∀ e, MeasurableSet (s e)) :
-- imply
  IsFiniteCoordinateSet (Set.pi Set.univ s) := by
-- proof
  apply StatMech.FrontierA.rectangle_isFiniteCoordinateSet s hs

/--
[generateFrom_isFiniteCoordinateSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma generateFrom_isFiniteCoordinateSet_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E] :
-- imply
  (inferInstance : MeasurableSpace (∀ e, S e)) = MeasurableSpace.generateFrom {A : Set (∀ e, S e) | IsFiniteCoordinateSet A} := by
-- proof
  apply StatMech.FrontierA.generateFrom_isFiniteCoordinateSet

/--
[exists_finiteCoordinateSet_symmDiff_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma exists_finiteCoordinateSet_symmDiff_lt_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
  {A : Set (∀ e, S e)}
  {eps : ENNReal}
-- given
  (mu : ∀ e, Measure (S e))
  (hA : MeasurableSet A)
  (heps : 0 < eps) :
-- imply
  ∃ B, IsFiniteCoordinateSet B ∧ Measure.pi mu (B ∆ A) < eps := by
-- proof
  apply StatMech.FrontierA.exists_finiteCoordinateSet_symmDiff_lt mu hA heps

/--
[measurable_piExtendOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma measurable_piExtendOn_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
-- given
  (base : ∀ e, S e) :
-- imply
  Measurable (piExtendOn K base) := by
-- proof
  apply StatMech.FrontierA.measurable_piExtendOn K base

/--
[piExtendOn_agreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma piExtendOn_agreeOn_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
-- given
  (base : ∀ e, S e)
  (x : ∀ e, S e) :
-- imply
  piAgreeOn K x (piExtendOn K base (piRestrict K x)) := by
-- proof
  apply StatMech.FrontierA.piExtendOn_agreeOn K base x

/--
[measurePreserving_piRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma measurePreserving_piRestrict_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
  {K : Set E}
-- given
  (mu : ∀ e, Measure (S e)) :
-- imply
  MeasurePreserving (piRestrict (S := S) K) (Measure.pi mu) (Measure.pi fun i : {e : E // e ∈ K} => mu i) := by
-- proof
  apply StatMech.FrontierA.measurePreserving_piRestrict mu K

/--
[IsFiniteCoordinateSet.preimage_piRestrict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma preimage_piRestrict_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {A : Set (∀ i : {e : E // e ∈ K}, S i)}
-- given
  (hA : IsFiniteCoordinateSet A) :
-- imply
  IsFiniteCoordinateSet ((piRestrict (S := S) K) ⁻¹' A) := by
-- proof
  apply StatMech.FrontierA.IsFiniteCoordinateSet.preimage_piRestrict K hA

/--
[exists_finiteCoordinateSet_dependsOn_symmDiff_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma exists_finiteCoordinateSet_dependsOn_symmDiff_lt_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
  {K : Set E}
  {A : Set (∀ e, S e)}
  {eps : ENNReal}
-- given
  (mu : ∀ e, Measure (S e))
  (hA : MeasurableSet A)
  (hdep : PiSetDependsOn K A)
  (heps : 0 < eps) :
-- imply
  ∃ B, IsFiniteCoordinateSet B ∧ PiSetDependsOn K B ∧ Measure.pi mu (B ∆ A) < eps := by
-- proof
  apply StatMech.FrontierA.exists_finiteCoordinateSet_dependsOn_symmDiff_lt mu K hA hdep heps

/--
[measurable_piFunctionalFamilyMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma measurable_piFunctionalFamilyMax_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
-- given
  (F : Set E → (∀ e, S e) → ℝ)
  (hF : ∀ K, Measurable (F K)) :
-- imply
  Measurable (piFunctionalFamilyMax F) := by
-- proof
  apply StatMech.FrontierA.measurable_piFunctionalFamilyMax F hF

/--
[measurable_piFunctionalFamilyDisjointMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma measurable_piFunctionalFamilyDisjointMax_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
-- given
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF : ∀ K, Measurable (F K))
  (hG : ∀ K, Measurable (G K)) :
-- imply
  Measurable (piFunctionalFamilyDisjointMax F G) := by
-- proof
  apply StatMech.FrontierA.measurable_piFunctionalFamilyDisjointMax F G hF hG

/--
[measurable_piFunctionalFamilyDisjointMaxAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma measurable_piFunctionalFamilyDisjointMaxAt_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
-- given
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF : ∀ K, Measurable (F K))
  (hG : ∀ K, Measurable (G K)) :
-- imply
  Measurable (fun p : (∀ e, S e) × (∀ e, S e) => piFunctionalFamilyDisjointMaxAt F G p.1 p.2) := by
-- proof
  apply StatMech.FrontierA.measurable_piFunctionalFamilyDisjointMaxAt F G hF hG

/--
[piFunctionalFamilyMax_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma piFunctionalFamilyMax_le_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {C : ℝ}
-- given
  (F : Set E → (∀ e, S e) → ℝ)
  (hF : ∀ K x, F K x ≤ C)
  (x : ∀ e, S e) :
-- imply
  piFunctionalFamilyMax F x ≤ C := by
-- proof
  apply StatMech.FrontierA.piFunctionalFamilyMax_le F hF x

/--
[piFunctionalFamilyDisjointMax_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma piFunctionalFamilyDisjointMax_le_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {C D : ℝ}
-- given
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K x, F K x ≤ C)
  (hG : ∀ K x, G K x ≤ D)
  (x : ∀ e, S e) :
-- imply
  piFunctionalFamilyDisjointMax F G x ≤ C * D := by
-- proof
  apply StatMech.FrontierA.piFunctionalFamilyDisjointMax_le F G hF0 hG0 hF hG x

/--
[piFunctionalFamilyDisjointMaxAt_le_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma piFunctionalFamilyDisjointMaxAt_le_bound_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {C D : ℝ}
-- given
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K x, F K x ≤ C)
  (hG : ∀ K x, G K x ≤ D)
  (x y : ∀ e, S e) :
-- imply
  piFunctionalFamilyDisjointMaxAt F G x y ≤ C * D := by
-- proof
  apply StatMech.FrontierA.piFunctionalFamilyDisjointMaxAt_le_bound F G hF0 hG0 hF hG x y

/--
[tendsto_piFunctionalFamilyMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma tendsto_piFunctionalFamilyMax_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
-- given
  (F : ℕ → Set E → (∀ e, S e) → ℝ)
  (Flim : Set E → (∀ e, S e) → ℝ)
  (x : ∀ e, S e)
  (h : ∀ K, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x))) :
-- imply
  Tendsto (fun n => piFunctionalFamilyMax (F n) x) atTop (𝓝 (piFunctionalFamilyMax Flim x)) := by
-- proof
  apply StatMech.FrontierA.tendsto_piFunctionalFamilyMax F Flim x h

/--
[tendsto_piFunctionalFamilyDisjointMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma tendsto_piFunctionalFamilyDisjointMax_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
-- given
  (F G : ℕ → Set E → (∀ e, S e) → ℝ)
  (Flim Glim : Set E → (∀ e, S e) → ℝ)
  (x : ∀ e, S e)
  (hF : ∀ K, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)))
  (hG : ∀ K, Tendsto (fun n => G n K x) atTop (𝓝 (Glim K x))) :
-- imply
  Tendsto (fun n => piFunctionalFamilyDisjointMax (F n) (G n) x) atTop (𝓝 (piFunctionalFamilyDisjointMax Flim Glim x)) := by
-- proof
  apply StatMech.FrontierA.tendsto_piFunctionalFamilyDisjointMax F G Flim Glim x hF hG

/--
[tendsto_piFunctionalFamilyDisjointMaxAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma tendsto_piFunctionalFamilyDisjointMaxAt_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
-- given
  (F G : ℕ → Set E → (∀ e, S e) → ℝ)
  (Flim Glim : Set E → (∀ e, S e) → ℝ)
  (x y : ∀ e, S e)
  (hF : ∀ K, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)))
  (hG : ∀ K, Tendsto (fun n => G n K y) atTop (𝓝 (Glim K y))) :
-- imply
  Tendsto (fun n => piFunctionalFamilyDisjointMaxAt (F n) (G n) x y) atTop (𝓝 (piFunctionalFamilyDisjointMaxAt Flim Glim x y)) := by
-- proof
  apply StatMech.FrontierA.tendsto_piFunctionalFamilyDisjointMaxAt F G Flim Glim x y hF hG

/--
[measurableFamilyBKR_of_bounded_ae_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma measurableFamilyBKR_of_bounded_ae_limit_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
  {C D : ℝ}
-- given
  (mu : ∀ e, Measure (S e))
  (F G : ℕ → Set E → (∀ e, S e) → ℝ)
  (Flim Glim : Set E → (∀ e, S e) → ℝ)
  (hC0 : 0 ≤ C)
  (hD0 : 0 ≤ D)
  (hFm : ∀ n K, Measurable (F n K))
  (hGm : ∀ n K, Measurable (G n K))
  (hFlimm : ∀ K, Measurable (Flim K))
  (hGlimm : ∀ K, Measurable (Glim K))
  (hF0 : ∀ n K x, 0 ≤ F n K x)
  (hG0 : ∀ n K x, 0 ≤ G n K x)
  (hFlim0 : ∀ K x, 0 ≤ Flim K x)
  (hGlim0 : ∀ K x, 0 ≤ Glim K x)
  (hFC : ∀ n K x, F n K x ≤ C)
  (hGD : ∀ n K x, G n K x ≤ D)
  (hFlimC : ∀ K x, Flim K x ≤ C)
  (hGlimD : ∀ K x, Glim K x ≤ D)
  (hconvF : ∀ K, ∀ᵐ x ∂Measure.pi mu, Tendsto (fun n => F n K x) atTop (𝓝 (Flim K x)))
  (hconvG : ∀ K, ∀ᵐ x ∂Measure.pi mu, Tendsto (fun n => G n K x) atTop (𝓝 (Glim K x)))
  (hineq : ∀ n, (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax (F n) (G n) x) ∂Measure.pi mu) ≤ (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (F n) x) ∂Measure.pi mu) * ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (G n) x) ∂Measure.pi mu ∧ (∫⁻ p, ENNReal.ofReal (piFunctionalFamilyDisjointMaxAt (F n) (G n) p.1 p.2) ∂(Measure.pi mu).prod (Measure.pi mu)) ≤ ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax (F n) x * piFunctionalFamilyMax (G n) x) ∂Measure.pi mu) :
-- imply
  (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax Flim Glim x) ∂Measure.pi mu) ≤ (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Flim x) ∂Measure.pi mu) * ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Glim x) ∂Measure.pi mu ∧ (∫⁻ p, ENNReal.ofReal (piFunctionalFamilyDisjointMaxAt Flim Glim p.1 p.2) ∂(Measure.pi mu).prod (Measure.pi mu)) ≤ ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax Flim x * piFunctionalFamilyMax Glim x) ∂Measure.pi mu := by
-- proof
  apply StatMech.FrontierA.measurableFamilyBKR_of_bounded_ae_limit mu F G Flim Glim C D hC0 hD0 hFm hGm hFlimm hGlimm hF0 hG0 hFlim0 hGlim0 hFC hGD hFlimC hGlimD hconvF hconvG hineq

/--
[finiteQuotientRepresentative_rightInverse](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma finiteQuotientRepresentative_rightInverse_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Nonempty (S e)]
  {n : E → ℕ}
  {e : E}
  {x : S e}
-- given
  (q : ∀ e, S e → Fin (n e)) :
-- imply
  q e (finiteQuotientRepresentative q e (q e x)) = q e x := by
-- proof
  apply StatMech.FrontierA.finiteQuotientRepresentative_rightInverse q e x

/--
[functionalFamilyBKR_of_finiteCoordinateFactors_and_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma functionalFamilyBKR_of_finiteCoordinateFactors_and_dual_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
-- given
  (mu : ∀ e, Measure (S e))
  (F G : Set E → (∀ e, S e) → ℝ)
  (fF : ∀ K, FiniteCoordinateFactorOn.{u, v, wF} K (F K))
  (fG : ∀ K, FiniteCoordinateFactorOn.{u, v, wG} K (G K))
  (hF0 : ∀ K y, 0 ≤ (fF K).H y)
  (hG0 : ∀ K y, 0 ≤ (fG K).H y) :
-- imply
  (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x) ∂Measure.pi mu) ≤ (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi mu) * ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi mu ∧ (∫⁻ p, ENNReal.ofReal (piFunctionalFamilyDisjointMaxAt F G p.1 p.2) ∂(Measure.pi mu).prod (Measure.pi mu)) ≤ ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) ∂Measure.pi mu := by
-- proof
  apply StatMech.FrontierA.functionalFamilyBKR_of_finiteCoordinateFactors_and_dual mu F G fF fG hF0 hG0

/--
[FiniteCoordinateFactorOn.measurable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma measurable_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {h : (∀ e, S e) → ℝ}
  {f : FiniteCoordinateFactorOn K h} :
-- imply
  Measurable h := by
-- proof
  apply StatMech.FrontierA.FiniteCoordinateFactorOn.measurable f

/--
[FiniteCoordinateFactorOn.nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma nonneg_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {h : (∀ e, S e) → ℝ}
  {f : FiniteCoordinateFactorOn K h} :
-- imply
  ∀ x, 0 ≤ h x := by
-- proof
  apply StatMech.FrontierA.FiniteCoordinateFactorOn.nonneg f

/--
[exists_finiteFactor_approx_simple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma exists_finiteFactor_approx_simple_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
  {K : Set E}
  {C : ℝ}
  {eps : ENNReal}
-- given
  (mu : ∀ e, Measure (S e))
  (s : SimpleFunc (∀ e, S e) ℝ)
  (hs0 : ∀ x, 0 ≤ s x)
  (hsC : ∀ x, s x ≤ C)
  (hsdep : PiDependsOn K s)
  (heps : 0 < eps) :
-- imply
  ∃ (t : (∀ e, S e) → ℝ) (f : FiniteCoordinateFactorOn.{u, v, 0} K t), (∀ x, t x ≤ C) ∧ Measure.pi mu {x | t x ≠ s x} < eps := by
-- proof
  apply StatMech.FrontierA.exists_finiteFactor_approx_simple mu K s hs0 hsC hsdep heps

/--
[exists_finiteFactor_approx_bounded](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma exists_finiteFactor_approx_bounded_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
  {K : Set E}
  {C : ℝ}
-- given
  (mu : ∀ e, Measure (S e))
  (h : (∀ e, S e) → ℝ)
  (hh : Measurable h)
  (hh0 : ∀ x, 0 ≤ h x)
  (hhC : ∀ x, h x ≤ C)
  (hhdep : PiDependsOn K h) :
-- imply
  ∃ (t : ℕ → (∀ e, S e) → ℝ) (f : ∀ n, FiniteCoordinateFactorOn.{u, v, 0} K (t n)), (∀ n x, t n x ≤ C) ∧ ∀ᵐ x ∂Measure.pi mu, Tendsto (fun n => t n x) atTop (𝓝 (h x)) := by
-- proof
  apply StatMech.FrontierA.exists_finiteFactor_approx_bounded mu K h hh hh0 hhC hhdep

/--
[measurableFamilyBKR_bounded_and_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductApprox.lean)
-/
@[path]
private lemma measurableFamilyBKR_bounded_and_dual_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (mu e)]
  {C D : ℝ}
-- given
  (mu : ∀ e, Measure (S e))
  (F G : Set E → (∀ e, S e) → ℝ)
  (hFm : ∀ K, Measurable (F K))
  (hGm : ∀ K, Measurable (G K))
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hFdep : ∀ K, PiDependsOn K (F K))
  (hGdep : ∀ K, PiDependsOn K (G K))
  (hC0 : 0 ≤ C)
  (hD0 : 0 ≤ D)
  (hFC : ∀ K x, F K x ≤ C)
  (hGD : ∀ K x, G K x ≤ D) :
-- imply
  (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G x) ∂Measure.pi mu) ≤ (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x) ∂Measure.pi mu) * ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G x) ∂Measure.pi mu ∧ (∫⁻ p, ENNReal.ofReal (piFunctionalFamilyDisjointMaxAt F G p.1 p.2) ∂(Measure.pi mu).prod (Measure.pi mu)) ≤ ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) ∂Measure.pi mu := by
-- proof
  apply StatMech.FrontierA.measurableFamilyBKR_bounded_and_dual mu F G hFm hGm hF0 hG0 hFdep hGdep C D hC0 hD0 hFC hGD


-- created on 2026-10-23
