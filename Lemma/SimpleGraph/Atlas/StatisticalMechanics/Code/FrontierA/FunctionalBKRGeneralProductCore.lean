import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.FunctionalBKRGeneralProductCore.Part10
open MeasureTheory Set Filter Topology StatMech StatMech.FrontierA


/--
[piFiberAssemble_apply_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFiberAssemble_apply_mem_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {e : E}
-- given
  (x : ∀ e, S e)
  (z : PiFiberFreeConfig (S := S) K)
  (he : e ∈ K) :
-- imply
  piFiberAssemble K x z e = x e := by
-- proof
  apply StatMech.FrontierA.piFiberAssemble_apply_mem K x z he

/--
[piFiberAssemble_apply_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFiberAssemble_apply_notMem_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {e : E}
-- given
  (x : ∀ e, S e)
  (z : PiFiberFreeConfig (S := S) K)
  (he : e ∉ K) :
-- imply
  piFiberAssemble K x z e = z ⟨e, he⟩ := by
-- proof
  apply StatMech.FrontierA.piFiberAssemble_apply_notMem K x z he

/--
[measurable_piFiberAssemble_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma measurable_piFiberAssemble_right_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
-- given
  (x : ∀ e, S e) :
-- imply
  Measurable (piFiberAssemble K x) := by
-- proof
  apply StatMech.FrontierA.measurable_piFiberAssemble_right K x

/--
[measurable_piFiberAssemble_uncurry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma measurable_piFiberAssemble_uncurry_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E} :
-- imply
  Measurable (Function.uncurry (piFiberAssemble (S := S) K)) := by
-- proof
  apply StatMech.FrontierA.measurable_piFiberAssemble_uncurry K

/--
[piFiberAssemble_piEquiv_symm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFiberAssemble_piEquiv_symm_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
-- given
  (u : ∀ i : {e : E // e ∈ K}, S i)
  (v w : PiFiberFreeConfig (S := S) K) :
-- imply
  piFiberAssemble K ((piFiberSplit (S := S) K).symm (u, v)) w = (piFiberSplit (S := S) K).symm (u, w) := by
-- proof
  apply StatMech.FrontierA.piFiberAssemble_piEquiv_symm K u v w

/--
[ae_isCoboundedUnder_ge_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma ae_isCoboundedUnder_ge_real_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [MeasurableSpace Ω]
  {ν : Measure Ω}
  [IsProbabilityMeasure ν]
  {f : Ω → ℝ} :
-- imply
  Filter.IsCoboundedUnder (fun a b : ℝ => a ≥ b) (ae ν) f := by
-- proof
  apply StatMech.FrontierA.ae_isCoboundedUnder_ge_real ν f

/--
[piCylinderEssInf_eq_of_piAgreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piCylinderEssInf_eq_of_piAgreeOn_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {K : Set E}
  {x y : ∀ e, S e}
-- given
  (μ : ∀ e, Measure (S e))
  (f : (∀ e, S e) → ℝ)
  (hxy : piAgreeOn K x y) :
-- imply
  piCylinderEssInf μ f K x = piCylinderEssInf μ f K y := by
-- proof
  apply StatMech.FrontierA.piCylinderEssInf_eq_of_piAgreeOn μ f K hxy

/--
[piCylinderEssInf_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piCylinderEssInf_nonneg_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
  {K : Set E}
-- given
  (μ : ∀ e, Measure (S e))
  (f : (∀ e, S e) → ℝ)
  (hf0 : ∀ x, 0 ≤ f x)
  (x : ∀ e, S e) :
-- imply
  0 ≤ piCylinderEssInf μ f K x := by
-- proof
  apply StatMech.FrontierA.piCylinderEssInf_nonneg μ f hf0 K x

/--
[measurable_piCylinderSublevelMeasure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma measurable_piCylinderSublevelMeasure_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
  {K : Set E}
  {r : ℝ}
-- given
  (μ : ∀ e, Measure (S e))
  (f : (∀ e, S e) → ℝ)
  (hf : Measurable f) :
-- imply
  Measurable (piCylinderSublevelMeasure μ f K r) := by
-- proof
  apply StatMech.FrontierA.measurable_piCylinderSublevelMeasure μ f hf K r

/--
[lt_piCylinderEssInf_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma lt_piCylinderEssInf_iff_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
  {K : Set E}
  {a : ℝ}
-- given
  (μ : ∀ e, Measure (S e))
  (f : (∀ e, S e) → ℝ)
  (hf0 : ∀ x, 0 ≤ f x)
  (x : ∀ e, S e) :
-- imply
  a < piCylinderEssInf μ f K x ↔ ∃ n : ℕ, piCylinderSublevelMeasure μ f K (a + 1 / (n + 1 : ℝ)) x = 0 := by
-- proof
  apply StatMech.FrontierA.lt_piCylinderEssInf_iff μ f hf0 K x a

/--
[measurable_piCylinderEssInf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma measurable_piCylinderEssInf_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
  {K : Set E}
-- given
  (μ : ∀ e, Measure (S e))
  (f : (∀ e, S e) → ℝ)
  (hf : Measurable f)
  (hf0 : ∀ x, 0 ≤ f x) :
-- imply
  Measurable (piCylinderEssInf μ f K) := by
-- proof
  apply StatMech.FrontierA.measurable_piCylinderEssInf μ f hf hf0 K

/--
[piCylinderEssInf_le_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piCylinderEssInf_le_ae_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
  {K : Set E}
-- given
  (μ : ∀ e, Measure (S e))
  (f : (∀ e, S e) → ℝ)
  (hf : Measurable f)
  (hf0 : ∀ x, 0 ≤ f x) :
-- imply
  ∀ᵐ x ∂Measure.pi μ, piCylinderEssInf μ f K x ≤ f x := by
-- proof
  apply StatMech.FrontierA.piCylinderEssInf_le_ae μ f hf hf0 K

/--
[piFunctionalDisjointEssMaxAt_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFunctionalDisjointEssMaxAt_nonneg_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
-- given
  (μ : ∀ e, Measure (S e))
  (f g : (∀ e, S e) → ℝ)
  (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x)
  (x y : ∀ e, S e) :
-- imply
  0 ≤ piFunctionalDisjointEssMaxAt μ f g x y := by
-- proof
  apply StatMech.FrontierA.piFunctionalDisjointEssMaxAt_nonneg μ f g hf0 hg0 x y

/--
[measurable_piFunctionalDisjointEssMaxAt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma measurable_piFunctionalDisjointEssMaxAt_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
-- given
  (μ : ∀ e, Measure (S e))
  (f g : (∀ e, S e) → ℝ)
  (hf : Measurable f)
  (hg : Measurable g)
  (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
-- imply
  Measurable (fun p : (∀ e, S e) × (∀ e, S e) => piFunctionalDisjointEssMaxAt μ f g p.1 p.2) := by
-- proof
  apply StatMech.FrontierA.measurable_piFunctionalDisjointEssMaxAt μ f g hf hg hf0 hg0

/--
[measurable_piFunctionalDisjointEssMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma measurable_piFunctionalDisjointEssMax_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
-- given
  (μ : ∀ e, Measure (S e))
  (f g : (∀ e, S e) → ℝ)
  (hf : Measurable f)
  (hg : Measurable g)
  (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
-- imply
  Measurable (piFunctionalDisjointEssMax μ f g) := by
-- proof
  apply StatMech.FrontierA.measurable_piFunctionalDisjointEssMax μ f g hf hg hf0 hg0

/--
[piFunctionalFamilyMax_cylinder_le_ae](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFunctionalFamilyMax_cylinder_le_ae_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
-- given
  (μ : ∀ e, Measure (S e))
  (f : (∀ e, S e) → ℝ)
  (hf : Measurable f)
  (hf0 : ∀ x, 0 ≤ f x) :
-- imply
  ∀ᵐ x ∂Measure.pi μ, piFunctionalFamilyMax (fun K => piCylinderEssInf μ f K) x ≤ f x := by
-- proof
  apply StatMech.FrontierA.piFunctionalFamilyMax_cylinder_le_ae μ f hf hf0

/--
[piFunctionalFamilyMax_cylinder_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFunctionalFamilyMax_cylinder_nonneg_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
-- given
  (μ : ∀ e, Measure (S e))
  (f : (∀ e, S e) → ℝ)
  (hf0 : ∀ x, 0 ≤ f x)
  (x : ∀ e, S e) :
-- imply
  0 ≤ piFunctionalFamilyMax (fun K => piCylinderEssInf μ f K) x := by
-- proof
  apply StatMech.FrontierA.piFunctionalFamilyMax_cylinder_nonneg μ f hf0 x

/--
[functionalBKR_generalProduct_of_familyBKR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma functionalBKR_generalProduct_of_familyBKR_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
-- given
  (μ : ∀ e, Measure (S e))
  (hBKR : HasMeasurableFunctionalBKR μ)
  (f g : (∀ e, S e) → ℝ)
  (hf : Measurable f)
  (hg : Measurable g)
  (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
-- imply
  (∫⁻ x, ENNReal.ofReal (piFunctionalDisjointEssMax μ f g x) ∂Measure.pi μ) ≤ (∫⁻ x, ENNReal.ofReal (f x) ∂Measure.pi μ) * ∫⁻ x, ENNReal.ofReal (g x) ∂Measure.pi μ := by
-- proof
  apply StatMech.FrontierA.functionalBKR_generalProduct_of_familyBKR μ hBKR f g hf hg hf0 hg0

/--
[dualFunctionalBKR_generalProduct_of_familyBKR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma dualFunctionalBKR_generalProduct_of_familyBKR_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [∀ e, IsProbabilityMeasure (μ e)]
-- given
  (μ : ∀ e, Measure (S e))
  (hBKR : HasMeasurableDualFunctionalBKR μ)
  (f g : (∀ e, S e) → ℝ)
  (hf : Measurable f)
  (hg : Measurable g)
  (hf0 : ∀ x, 0 ≤ f x)
  (hg0 : ∀ x, 0 ≤ g x) :
-- imply
  (∫⁻ p, ENNReal.ofReal (piFunctionalDisjointEssMaxAt μ f g p.1 p.2) ∂(Measure.pi μ).prod (Measure.pi μ)) ≤ ∫⁻ x, ENNReal.ofReal (f x * g x) ∂Measure.pi μ := by
-- proof
  apply StatMech.FrontierA.dualFunctionalBKR_generalProduct_of_familyBKR μ hBKR f g hf hg hf0 hg0

/--
[piFunctionalFamilyMax_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFunctionalFamilyMax_nonneg_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
-- given
  (F : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (x : ∀ e, S e) :
-- imply
  0 ≤ piFunctionalFamilyMax F x := by
-- proof
  apply StatMech.FrontierA.piFunctionalFamilyMax_nonneg F hF0 x

/--
[familyMember_le_cylinderMin_familyMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma familyMember_le_cylinderMin_familyMax_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {F : Set E → StatMech.ConfigSpace E → ℝ}
  {K : Set E}
  {omega : StatMech.ConfigSpace E}
-- given
  (hF : ∀ K, PiDependsOn K (F K)) :
-- imply
  F K omega ≤ cylinderMin (piFunctionalFamilyMax F) K omega := by
-- proof
  apply StatMech.FrontierA.familyMember_le_cylinderMin_familyMax F hF K omega

/--
[piFunctionalFamilyDisjointMaxAt_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFunctionalFamilyDisjointMaxAt_le_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {F G : Set E → StatMech.ConfigSpace E → ℝ}
  {omega eta : StatMech.ConfigSpace E}
-- given
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  piFunctionalFamilyDisjointMaxAt F G omega eta ≤ functionalDisjointMaxAt (piFunctionalFamilyMax F) (piFunctionalFamilyMax G) omega eta := by
-- proof
  apply StatMech.FrontierA.piFunctionalFamilyDisjointMaxAt_le F G hF0 hG0 hF hG omega eta

/--
[functionalFamilyBKR_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma functionalFamilyBKR_real_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {F G : Set E → StatMech.ConfigSpace E → ℝ}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  productExpectation phi (piFunctionalFamilyDisjointMax F G) ≤ productExpectation phi (piFunctionalFamilyMax F) * productExpectation phi (piFunctionalFamilyMax G) := by
-- proof
  apply StatMech.FrontierA.functionalFamilyBKR_real phi hphi0 hphi1 F G hF0 hG0 hF hG

/--
[dualFunctionalFamilyBKR_real](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma dualFunctionalFamilyBKR_real_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {phi : E → Bool → ℝ}
  {F G : Set E → StatMech.ConfigSpace E → ℝ}
-- given
  (hphi0 : ∀ e b, 0 ≤ phi e b)
  (hphi1 : ∀ e, phi e false + phi e true = 1)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  dualProductExpectation phi (fun p => piFunctionalFamilyDisjointMaxAt F G p.1 p.2) ≤ productExpectation phi (fun x => piFunctionalFamilyMax F x * piFunctionalFamilyMax G x) := by
-- proof
  apply StatMech.FrontierA.dualFunctionalFamilyBKR_real phi hphi0 hphi1 F G hF0 hG0 hF hG

/--
[productExpectation_fin_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma productExpectation_fin_cons_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {phi : Fin (n + 1) → Bool → ℝ}
  {H : (Fin (n + 1) → Bool) → ℝ} :
-- imply
  productExpectation phi H = ∑ b : Bool, phi 0 b * productExpectation (fun i b => phi i.succ b) (fun eta => H (Fin.cons b eta)) := by
-- proof
  apply StatMech.FrontierA.productExpectation_fin_cons phi H

/--
[HasBernoulliBlockRepresentation.equiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma equiv_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [Fintype T]
  [Fintype U]
  {e : T ≃ U}
  {w : U → ℝ}
-- given
  (h : HasBernoulliBlockRepresentation (fun t => w (e t))) :
-- imply
  HasBernoulliBlockRepresentation w := by
-- proof
  apply StatMech.FrontierA.HasBernoulliBlockRepresentation.equiv e w h

/--
[productExpectation_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma productExpectation_const_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [Fintype I]
  [DecidableEq I]
  {phi : I → Bool → ℝ}
  {c : ℝ}
-- given
  (hphi1 : ∀ i, phi i false + phi i true = 1) :
-- imply
  productExpectation phi (fun _ => c) = c := by
-- proof
  apply StatMech.FrontierA.productExpectation_const phi hphi1 c

/--
[hasBernoulliBlockRepresentation_option](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma hasBernoulliBlockRepresentation_option_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  [Fintype T]
  [Nonempty T]
  {w : Option T → ℝ}
-- given
  (ih : ∀ (v : T → ℝ), (∀ t, 0 ≤ v t) → (∑ t, v t) = 1 → HasBernoulliBlockRepresentation v)
  (hw0 : ∀ t, 0 ≤ w t)
  (hw1 : (∑ t, w t) = 1) :
-- imply
  HasBernoulliBlockRepresentation w := by
-- proof
  apply StatMech.FrontierA.hasBernoulliBlockRepresentation_option ih w hw0 hw1

/--
[exists_bernoulliBlockRepresentation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma exists_bernoulliBlockRepresentation_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {T : Type u}
  [Fintype T]
  {w : T → ℝ}
-- given
  (hw0 : ∀ t, 0 ≤ w t)
  (hw1 : (∑ t, w t) = 1) :
-- imply
  HasBernoulliBlockRepresentation w := by
-- proof
  apply StatMech.FrontierA.exists_bernoulliBlockRepresentation w hw0 hw1

/--
[familyMember_le_piCylinderMin_familyMax](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma familyMember_le_piCylinderMin_familyMax_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {K : Set E}
-- given
  (F : Set E → (∀ e, S e) → ℝ)
  (hF : ∀ K, PiDependsOn K (F K))
  (x : ∀ e, S e) :
-- imply
  F K x ≤ piCylinderMin (piFunctionalFamilyMax F) K x := by
-- proof
  apply StatMech.FrontierA.familyMember_le_piCylinderMin_familyMax F hF K x

/--
[piFunctionalFamilyDisjointMaxAt_le_pi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFunctionalFamilyDisjointMaxAt_le_pi_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
-- given
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K))
  (x y : ∀ e, S e) :
-- imply
  piFunctionalFamilyDisjointMaxAt F G x y ≤ piFunctionalDisjointMaxAt (piFunctionalFamilyMax F) (piFunctionalFamilyMax G) x y := by
-- proof
  apply StatMech.FrontierA.piFunctionalFamilyDisjointMaxAt_le_pi F G hF0 hG0 hF hG x y

/--
[dependentWholeBlocks_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma dependentWholeBlocks_disjoint_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {K L : Set E}
-- given
  (hKL : Disjoint K L) :
-- imply
  Disjoint (dependentWholeBlocks (D := D) K) (dependentWholeBlocks (D := D) L) := by
-- proof
  apply StatMech.FrontierA.dependentWholeBlocks_disjoint hKL

/--
[decodeDependentBlockConfig_encode](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma decodeDependentBlockConfig_encode_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (x : ∀ e, S e) :
-- imply
  decodeDependentBlockConfig decode (encodeDependentBlockConfig decode hdecode x) = x := by
-- proof
  apply StatMech.FrontierA.decodeDependentBlockConfig_encode decode hdecode x

/--
[liftDependentPiCylinder_agreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma liftDependentPiCylinder_agreeOn_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {K : Set E}
  {omega : StatMech.ConfigSpace (Sigma D)}
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (x : ∀ e, S e) :
-- imply
  agreeOn (dependentWholeBlocks (D := D) K) omega (liftDependentPiCylinder decode hdecode K omega x) := by
-- proof
  apply StatMech.FrontierA.liftDependentPiCylinder_agreeOn decode hdecode K omega x

/--
[decodeDependentBlockConfig_lift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma decodeDependentBlockConfig_lift_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {K : Set E}
  {omega : StatMech.ConfigSpace (Sigma D)}
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (x : ∀ e, S e)
  (hx : piAgreeOn K (decodeDependentBlockConfig decode omega) x) :
-- imply
  decodeDependentBlockConfig decode (liftDependentPiCylinder decode hdecode K omega x) = x := by
-- proof
  apply StatMech.FrontierA.decodeDependentBlockConfig_lift decode hdecode K omega x hx

/--
[piAgreeOn_decodeDependent_of_agreeOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piAgreeOn_decodeDependent_of_agreeOn_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {K : Set E}
  {omega eta : StatMech.ConfigSpace (Sigma D)}
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (h : agreeOn (dependentWholeBlocks (D := D) K) omega eta) :
-- imply
  piAgreeOn K (decodeDependentBlockConfig decode omega) (decodeDependentBlockConfig decode eta) := by
-- proof
  apply StatMech.FrontierA.piAgreeOn_decodeDependent_of_agreeOn decode K h

/--
[piCylinderMin_decodeDependentBlockConfig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piCylinderMin_decodeDependentBlockConfig_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {K : Set E}
  {omega : StatMech.ConfigSpace (Sigma D)}
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (f : (∀ e, S e) → ℝ) :
-- imply
  piCylinderMin f K (decodeDependentBlockConfig decode omega) = cylinderMin (f ∘ decodeDependentBlockConfig decode) (dependentWholeBlocks (D := D) K) omega := by
-- proof
  apply StatMech.FrontierA.piCylinderMin_decodeDependentBlockConfig decode hdecode f K omega

/--
[piFunctionalDisjointMaxAt_decodeDependent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFunctionalDisjointMaxAt_decodeDependent_le_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {omega eta : StatMech.ConfigSpace (Sigma D)}
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (f g : (∀ e, S e) → ℝ) :
-- imply
  piFunctionalDisjointMaxAt f g (decodeDependentBlockConfig decode omega) (decodeDependentBlockConfig decode eta) ≤ functionalDisjointMaxAt (f ∘ decodeDependentBlockConfig decode) (g ∘ decodeDependentBlockConfig decode) omega eta := by
-- proof
  apply StatMech.FrontierA.piFunctionalDisjointMaxAt_decodeDependent_le decode hdecode f g omega eta

/--
[piFunctionalDisjointMax_decodeDependent_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma piFunctionalDisjointMax_decodeDependent_le_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {omega : StatMech.ConfigSpace (Sigma D)}
-- given
  (decode : ∀ e, (D e → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (f g : (∀ e, S e) → ℝ) :
-- imply
  piFunctionalDisjointMax f g (decodeDependentBlockConfig decode omega) ≤ functionalDisjointMax (f ∘ decodeDependentBlockConfig decode) (g ∘ decodeDependentBlockConfig decode) omega := by
-- proof
  apply StatMech.FrontierA.piFunctionalDisjointMax_decodeDependent_le decode hdecode f g omega

/--
[functionalFamilyBKR_dependentBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma functionalFamilyBKR_dependentBlocks_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {phi : Sigma D → Bool → ℝ}
-- given
  (hphi0 : ∀ z b, 0 ≤ phi z b)
  (hphi1 : ∀ z, phi z false + phi z true = 1)
  (decode : ∀ e, (D e → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  productExpectation phi (fun omega => piFunctionalFamilyDisjointMax F G (decodeDependentBlockConfig decode omega)) ≤ productExpectation phi (fun omega => piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega)) * productExpectation phi (fun omega => piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := by
-- proof
  apply StatMech.FrontierA.functionalFamilyBKR_dependentBlocks phi hphi0 hphi1 decode hdecode F G hF0 hG0 hF hG

/--
[dualFunctionalFamilyBKR_dependentBlocks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/FunctionalBKRGeneralProductCore.lean)
-/
@[path]
private lemma dualFunctionalFamilyBKR_dependentBlocks_eq
  {E : Type u}
  [Fintype E]
  [DecidableEq E]
  {D : E → Type*}
  [∀ e, Fintype (D e)]
  [∀ e, DecidableEq (D e)]
  {phi : Sigma D → Bool → ℝ}
-- given
  (hphi0 : ∀ z b, 0 ≤ phi z b)
  (hphi1 : ∀ z, phi z false + phi z true = 1)
  (decode : ∀ e, (D e → Bool) → S e)
  (hdecode : ∀ e, Function.Surjective (decode e))
  (F G : Set E → (∀ e, S e) → ℝ)
  (hF0 : ∀ K x, 0 ≤ F K x)
  (hG0 : ∀ K x, 0 ≤ G K x)
  (hF : ∀ K, PiDependsOn K (F K))
  (hG : ∀ K, PiDependsOn K (G K)) :
-- imply
  dualProductExpectation phi (fun pair => piFunctionalFamilyDisjointMaxAt F G (decodeDependentBlockConfig decode pair.1) (decodeDependentBlockConfig decode pair.2)) ≤ productExpectation phi (fun omega => piFunctionalFamilyMax F (decodeDependentBlockConfig decode omega) * piFunctionalFamilyMax G (decodeDependentBlockConfig decode omega)) := by
-- proof
  apply StatMech.FrontierA.dualFunctionalFamilyBKR_dependentBlocks phi hphi0 hphi1 decode hdecode F G hF0 hG0 hF hG


-- created on 2026-10-23
