import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductFinite
open MeasureTheory Set Filter Topology StatMech StatMech.FrontierA


/--
[functionalFamilyBKR_finiteProduct_primal_of_blocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma functionalFamilyBKR_finiteProduct_primal_of_blocks_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Fintype (S e)]
  {n : E → ℕ}
-- given
  (w : ∀ e, S e → ℝ)
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K))
  (Phi : Sigma (fun e => Fin (n e)) → Bool → ℝ)
  (decode : ∀ e, (Fin (n e) → Bool) → S e)
  (hPhi0 : ∀ z b, 0 ≤ Phi z b)
  (hPhi1 : ∀ z, Phi z false + Phi z true = 1)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (hexpect : ∀ e (h : S e → ℝ), productExpectation (fun d b => Phi ⟨e, d⟩ b) (h ∘ decode e) = ∑ s, w e s * h s) :
-- imply
  finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤ finitePiExpectation w (piFunctionalFamilyMax F) * finitePiExpectation w (piFunctionalFamilyMax G) := by
-- proof
  apply StatMech.FrontierA.functionalFamilyBKR_finiteProduct_primal_of_blocks w F G hF0 hG0 hF hG n Phi decode hPhi0 hPhi1 hdecode hexpect

/--
[functionalFamilyBKR_finiteProduct_primal_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma functionalFamilyBKR_finiteProduct_primal_of_data_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Fintype (S e)]
-- given
  (w : ∀ e, S e → ℝ)
  (hw0 : ∀ e s, 0 ≤ w e s)
  (hw1 : ∀ e, (∑ s, w e s) = 1)
  (rep : ∀ e, BernoulliBlockData (w e))
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤ finitePiExpectation w (piFunctionalFamilyMax F) * finitePiExpectation w (piFunctionalFamilyMax G) := by
-- proof
  apply StatMech.FrontierA.functionalFamilyBKR_finiteProduct_primal_of_data w hw0 hw1 rep F G hF0 hG0 hF hG

/--
[functionalFamilyBKR_finiteProduct_primal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma functionalFamilyBKR_finiteProduct_primal_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Fintype (S e)]
-- given
  (w : ∀ e, S e → ℝ)
  (hw0 : ∀ e s, 0 ≤ w e s)
  (hw1 : ∀ e, (∑ s, w e s) = 1)
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤ finitePiExpectation w (piFunctionalFamilyMax F) * finitePiExpectation w (piFunctionalFamilyMax G) := by
-- proof
  apply StatMech.FrontierA.functionalFamilyBKR_finiteProduct_primal w hw0 hw1 F G hF0 hG0 hF hG

/--
[functionalFamilyBKR_finiteProduct_and_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma functionalFamilyBKR_finiteProduct_and_dual_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Fintype (S e)]
-- given
  (w : ∀ e, S e → ℝ)
  (hw0 : ∀ e s, 0 ≤ w e s)
  (hw1 : ∀ e, (∑ s, w e s) = 1)
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤ finitePiExpectation w (piFunctionalFamilyMax F) * finitePiExpectation w (piFunctionalFamilyMax G) ∧ finitePiDualExpectation w (fun pair => piFunctionalFamilyDisjointMaxAt F G pair.1 pair.2) ≤ finitePiExpectation w (fun x => piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) := by
-- proof
  apply StatMech.FrontierA.functionalFamilyBKR_finiteProduct_and_dual w hw0 hw1 F G hF0 hG0 hF hG

/--
[functionalFamilyBKR_finiteProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma functionalFamilyBKR_finiteProduct_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Fintype (S e)]
-- given
  (w : ∀ e, S e → ℝ)
  (hw0 : ∀ e s, 0 ≤ w e s)
  (hw1 : ∀ e, (∑ s, w e s) = 1)
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  finitePiExpectation w (piFunctionalFamilyDisjointMax F G) ≤ finitePiExpectation w (piFunctionalFamilyMax F) * finitePiExpectation w (piFunctionalFamilyMax G) := by
-- proof
  apply StatMech.FrontierA.functionalFamilyBKR_finiteProduct w hw0 hw1 F G hF0 hG0 hF hG

/--
[dualFunctionalFamilyBKR_finiteProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma dualFunctionalFamilyBKR_finiteProduct_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Fintype (S e)]
-- given
  (w : ∀ e, S e → ℝ)
  (hw0 : ∀ e s, 0 ≤ w e s)
  (hw1 : ∀ e, (∑ s, w e s) = 1)
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  finitePiDualExpectation w (fun pair => piFunctionalFamilyDisjointMaxAt F G pair.1 pair.2) ≤ finitePiExpectation w (fun x => piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) := by
-- proof
  apply StatMech.FrontierA.dualFunctionalFamilyBKR_finiteProduct w hw0 hw1 F G hF0 hG0 hF hG

/--
[finitePiExpectation_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma finitePiExpectation_nonneg_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Fintype (S e)]
  [∀ e, MeasurableSingletonClass (S e)]
-- given
  (w : ∀ e, S e → ℝ)
  (hw0 : ∀ e s, 0 ≤ w e s)
  (H : (∀ e, S e) → ℝ)
  (hH0 : ∀ x, 0 ≤ H x) :
-- imply
  0 ≤ finitePiExpectation w H := by
-- proof
  apply StatMech.FrontierA.finitePiExpectation_nonneg w hw0 H hH0

/--
[lintegral_finitePi_eq_ofReal_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma lintegral_finitePi_eq_ofReal_expectation_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Fintype (S e)]
  [∀ e, MeasurableSingletonClass (S e)]
  [∀ e, IsProbabilityMeasure (nu e)]
-- given
  (nu : ∀ e, Measure (S e))
  (H : (∀ e, S e) → ℝ)
  (hH0 : ∀ x, 0 ≤ H x) :
-- imply
  (∫⁻ x, ENNReal.ofReal (H x) ∂Measure.pi nu) = ENNReal.ofReal (finitePiExpectation (fun e s => (nu e {s}).toReal) H) := by
-- proof
  apply StatMech.FrontierA.lintegral_finitePi_eq_ofReal_expectation nu H hH0

/--
[lintegral_finitePiDual_eq_ofReal_expectation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma lintegral_finitePiDual_eq_ofReal_expectation_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, Fintype (S e)]
  [∀ e, MeasurableSingletonClass (S e)]
  [∀ e, IsProbabilityMeasure (nu e)]
-- given
  (nu : ∀ e, Measure (S e))
  (H : ((∀ e, S e) × (∀ e, S e)) → ℝ)
  (hH0 : ∀ p, 0 ≤ H p) :
-- imply
  (∫⁻ p, ENNReal.ofReal (H p) ∂(Measure.pi nu).prod (Measure.pi nu)) = ENNReal.ofReal (finitePiDualExpectation (fun e s => (nu e {s}).toReal) H) := by
-- proof
  apply StatMech.FrontierA.lintegral_finitePiDual_eq_ofReal_expectation nu H hH0

/--
[functionalFamilyBKR_finiteFactor_and_dual](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductFinite.lean)
-/
@[path]
private lemma functionalFamilyBKR_finiteFactor_and_dual_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {T : E → Type*}
  [∀ e, MeasurableSpace (T e)]
  [∀ e, IsProbabilityMeasure (mu e)]
-- given
  (mu : ∀ e, Measure (S e))
  (q : ∀ e, S e → T e)
  (hq : ∀ e, Measurable (q e))
  (F G : Set E → (∀ e, T e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyDisjointMax F G (fun e => q e (x e))) ∂Measure.pi mu) ≤ (∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F (fun e => q e (x e))) ∂Measure.pi mu) * ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax G (fun e => q e (x e))) ∂Measure.pi mu ∧ (∫⁻ p, ENNReal.ofReal (piFunctionalFamilyDisjointMaxAt F G (fun e => q e (p.1 e)) (fun e => q e (p.2 e))) ∂(Measure.pi mu).prod (Measure.pi mu)) ≤ ∫⁻ x, ENNReal.ofReal (piFunctionalFamilyMax F (fun e => q e (x e)) * piFunctionalFamilyMax G (fun e => q e (x e))) ∂Measure.pi mu := by
-- proof
  apply StatMech.FrontierA.functionalFamilyBKR_finiteFactor_and_dual mu q hq F G hF0 hG0 hF hG


-- created on 2026-10-23
