import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.PlusStateDLR.Part6
open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology StatMech StatMech.Ising


/--
[specApply_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma specApply_eq_sum_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {f : ConfigSpace (Site d) → ℝ}
  {ω : ConfigSpace (Site d)}
-- given
  (β h : ℝ) :
-- imply
  specApply n B β h f ω = ∑ τ : {x // x ∈ box d n} → Bool, fvProb ω n B β h τ * f (glue ω τ) := by
-- proof
  apply StatMech.Ising.specApply_eq_sum n B β h f ω

/--
[continuous_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma continuous_glue_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun ω : ConfigSpace (Site d) => glue ω τ) := by
-- proof
  apply StatMech.Ising.continuous_glue n τ

/--
[continuous_spin_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma continuous_spin_glue_eq
  {d : ℕ}
  {n : ℕ}
  {x : Site d}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun ω : ConfigSpace (Site d) => spin (glue ω τ) x) := by
-- proof
  apply StatMech.Ising.continuous_spin_glue n τ x

/--
[continuous_bond_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma continuous_bond_glue_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (Site d)}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun ω : ConfigSpace (Site d) => bond (glue ω τ) e) := by
-- proof
  apply StatMech.Ising.continuous_bond_glue n τ e

/--
[continuous_fvEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma continuous_fvEnergy_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun ω : ConfigSpace (Site d) => fvEnergy ω n B h τ) := by
-- proof
  apply StatMech.Ising.continuous_fvEnergy n B h τ

/--
[continuous_fvWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma continuous_fvWeight_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun ω : ConfigSpace (Site d) => fvWeight ω n B β h τ) := by
-- proof
  apply StatMech.Ising.continuous_fvWeight n B β h τ

/--
[continuous_fvZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma continuous_fvZ_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  Continuous (fun ω : ConfigSpace (Site d) => fvZ ω n B β h) := by
-- proof
  apply StatMech.Ising.continuous_fvZ n B β h

/--
[continuous_fvProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma continuous_fvProb_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Continuous (fun ω : ConfigSpace (Site d) => fvProb ω n B β h τ) := by
-- proof
  apply StatMech.Ising.continuous_fvProb n B β h τ

/--
[specApply_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma specApply_continuous_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {f : ConfigSpace (Site d) → ℝ}
-- given
  (β h : ℝ)
  (hf : Continuous f) :
-- imply
  Continuous (specApply n B β h f) := by
-- proof
  apply StatMech.Ising.specApply_continuous n B β h hf

/--
[specApply_bcf_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma specApply_bcf_apply_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
  {ω : ConfigSpace (Site d)}
-- given
  (β h : ℝ) :
-- imply
  specApply_bcf n B β h f ω = specApply n B β h (f : ConfigSpace (Site d) → ℝ) ω := by
-- proof
  apply StatMech.Ising.specApply_bcf_apply n B β h f ω

/--
[psdlr_specApply_integral_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma psdlr_specApply_integral_eq_eq
  {d : ℕ}
  {n : ℕ}
  {f : ConfigSpace (Site d) →ᵇ ℝ}
-- given
  (β h : ℝ)
  (hcons : FVConsistency d β h) :
-- imply
  ∫ ω, specApply n (bondFinsetTouch d n) β h (f : ConfigSpace (Site d) → ℝ) ω ∂(plusState d β h : Measure (ConfigSpace (Site d))) = ∫ ω, f ω ∂(plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.psdlr_specApply_integral_eq β h hcons n f

/--
[isingSpecFull_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma isingSpecFull_apply_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η : ConfigSpace (Site d)}
-- given
  (β h : ℝ) :
-- imply
  (isingSpecFull n B β h) η = fvMeasure η n B β h := by
-- proof
  apply StatMech.Ising.isingSpecFull_apply n B β h η

/--
[integral_bind_specApply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma integral_bind_specApply_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {μ : Measure (ConfigSpace (Site d))}
  [IsProbabilityMeasure μ]
  {f : ConfigSpace (Site d) →ᵇ ℝ}
-- given
  (β h : ℝ) :
-- imply
  ∫ y, f y ∂((isingSpecFull n B β h) ∘ₘ μ) = ∫ ω, specApply n B β h (f : ConfigSpace (Site d) → ℝ) ω ∂μ := by
-- proof
  apply StatMech.Ising.integral_bind_specApply n B β h μ f

/--
[psdlr_bind_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma psdlr_bind_eq_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (β h : ℝ)
  (hcons : FVConsistency d β h) :
-- imply
  (isingSpecFull n (bondFinsetTouch d n) β h) ∘ₘ (plusState d β h : Measure (ConfigSpace (Site d))) = (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.psdlr_bind_eq β h hcons n

/--
[outsideSigma_le_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma outsideSigma_le_invariant_eq
  {d : ℕ}
  [Countable E]
  {Λ : Set E} :
-- imply
  outsideSigma Λ ≤ outsideInvariantMS Λ := by
-- proof
  apply StatMech.Ising.outsideSigma_le_invariant Λ

/--
[glue_mem_iff_of_outsideSigma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma glue_mem_iff_of_outsideSigma_eq
  {d : ℕ}
  {n : ℕ}
  {s : Set (ConfigSpace (Site d))}
  {ω : ConfigSpace (Site d)}
-- given
  (hs : MeasurableSet[outsideSigma (box d n)] s)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  glue ω τ ∈ s ↔ ω ∈ s := by
-- proof
  apply StatMech.Ising.glue_mem_iff_of_outsideSigma n hs ω τ

/--
[fvMeasure_apply_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma fvMeasure_apply_eq_sum_eq
  {d : ℕ}
  {ω : ConfigSpace (Site d)}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {t : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (ht : MeasurableSet t) :
-- imply
  (fvMeasure ω n B β h) t = ∑ τ : {x // x ∈ box d n} → Bool, ENNReal.ofReal (fvProb ω n B β h τ) * (Set.indicator t (1 : ConfigSpace (Site d) → ℝ≥0∞) (glue ω τ)) := by
-- proof
  apply StatMech.Ising.fvMeasure_apply_eq_sum ω n B β h ht

/--
[fvMeasure_inter_outsideSigma](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma fvMeasure_inter_outsideSigma_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {s : Set (ConfigSpace (Site d))}
  {t : Set (ConfigSpace (Site d))}
  {ω : ConfigSpace (Site d)}
-- given
  (β h : ℝ)
  (hs : MeasurableSet[outsideSigma (box d n)] s)
  (ht : MeasurableSet t) :
-- imply
  (fvMeasure ω n B β h) (s ∩ t) = (Set.indicator s (1 : ConfigSpace (Site d) → ℝ≥0∞) ω) * (fvMeasure ω n B β h) t := by
-- proof
  apply StatMech.Ising.fvMeasure_inter_outsideSigma n B β h hs ht ω

/--
[psdlr_compProd_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma psdlr_compProd_rect_eq
  {d : ℕ}
  {n : ℕ}
  {s : Set (ConfigSpace (Site d))}
  {t : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hcons : FVConsistency d β h)
  (hs : MeasurableSet[outsideSigma (box d n)] s)
  (ht : MeasurableSet t) :
-- imply
  (((plusState d β h : Measure (ConfigSpace (Site d))).trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h)) (s ×ˢ t) = (plusState d β h : Measure (ConfigSpace (Site d))) (s ∩ t) := by
-- proof
  apply StatMech.Ising.psdlr_compProd_rect β h hcons n hs ht

/--
[psdlr_compProd_trim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma psdlr_compProd_trim_eq_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (β h : ℝ)
  (hcons : FVConsistency d β h) :
-- imply
  ((plusState d β h : Measure (ConfigSpace (Site d))).trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h) = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _ ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.psdlr_compProd_trim_eq β h hcons n

/--
[psdlr_plusState_isDLR](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/PlusStateDLR.lean)
-/
@[path]
private lemma psdlr_plusState_isDLR_eq
  {d : ℕ}
-- given
  (β h : ℝ)
  (hcons : FVConsistency d β h) :
-- imply
  IsDLRState d β h (plusState d β h : Measure (ConfigSpace (Site d))) := by
-- proof
  apply StatMech.Ising.psdlr_plusState_isDLR β h hcons


-- created on 2026-10-23
