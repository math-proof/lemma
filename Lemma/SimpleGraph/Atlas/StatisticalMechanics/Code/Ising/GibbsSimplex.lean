import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplex.Part3
open MeasureTheory ProbabilityTheory MeasurableSpace Set StatMech StatMech.Ising


/--
[measurableSet_mem_finInterSystem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma measurableSet_mem_finInterSystem_eq
  {d : ℕ}
  [MeasurableSpace Ω]
  {S : Set (Set Ω)}
  {t : Set Ω}
-- given
  (hSm : ∀ s ∈ S, MeasurableSet s)
  (ht : t ∈ finInterSystem S) :
-- imply
  MeasurableSet t := by
-- proof
  apply StatMech.Ising.measurableSet_mem_finInterSystem hSm ht

/--
[isPiSystem_finInterSystem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma isPiSystem_finInterSystem_eq
  {d : ℕ}
  {S : Set (Set Ω)} :
-- imply
  IsPiSystem (finInterSystem S) := by
-- proof
  apply StatMech.Ising.isPiSystem_finInterSystem S

/--
[generateFrom_finInterSystem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma generateFrom_finInterSystem_eq
  {d : ℕ}
  [mΩ : MeasurableSpace Ω]
  {S : Set (Set Ω)}
-- given
  (hgen : MeasurableSpace.generateFrom S = mΩ) :
-- imply
  MeasurableSpace.generateFrom (finInterSystem S) = mΩ := by
-- proof
  apply StatMech.Ising.generateFrom_finInterSystem hgen

/--
[kernel_ae_eq_trim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma kernel_ae_eq_trim_eq
  {d : ℕ}
  {mΩ : MeasurableSpace Ω}
  [hcg : @CountablyGenerated Ω mΩ]
  {m : MeasurableSpace Ω}
  {k₁ k₂ : @Kernel Ω Ω m mΩ}
  {μ : @Measure Ω mΩ}
  [IsFiniteMeasure μ]
-- given
  (hm : m ≤ mΩ)
  (hp1 : ∀ η, @IsProbabilityMeasure Ω mΩ (k₁ η))
  (hp2 : ∀ η, @IsProbabilityMeasure Ω mΩ (k₂ η))
  (h : k₁ =ᵐ[μ] k₂) :
-- imply
  k₁ =ᵐ[μ.trim hm] k₂ := by
-- proof
  apply StatMech.Ising.kernel_ae_eq_trim mΩ m hm k₁ k₂ μ hp1 hp2 h

/--
[trim_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma trim_smul_eq
  {d : ℕ}
  {m mΩ : MeasurableSpace Ω}
  {μ : @Measure Ω mΩ}
-- given
  (hm : m ≤ mΩ)
  (a : ℝ≥0∞) :
-- imply
  (a • μ).trim hm = a • (μ.trim hm) := by
-- proof
  apply StatMech.Ising.trim_smul μ hm a

/--
[meas_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_glue_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => glue η τ) := by
-- proof
  apply StatMech.Ising.meas_glue n τ

/--
[meas_glue_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_glue_eval_eq
  {d : ℕ}
  {n : ℕ}
  {x : Site d}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => (glue η τ) x) := by
-- proof
  apply StatMech.Ising.meas_glue_eval n τ x

/--
[meas_spin_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_spin_glue_eq
  {d : ℕ}
  {n : ℕ}
  {x : Site d}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => spin (glue η τ) x) := by
-- proof
  apply StatMech.Ising.meas_spin_glue n τ x

/--
[meas_bond_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_bond_glue_eq
  {d : ℕ}
  {n : ℕ}
  {e : Sym2 (Site d)}
-- given
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => bond (glue η τ) e) := by
-- proof
  apply StatMech.Ising.meas_bond_glue n τ e

/--
[meas_fvEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_fvEnergy_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => fvEnergy η n B h τ) := by
-- proof
  apply StatMech.Ising.meas_fvEnergy n B h τ

/--
[meas_fvWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_fvWeight_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => fvWeight η n B β h τ) := by
-- proof
  apply StatMech.Ising.meas_fvWeight n B β h τ

/--
[meas_fvZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_fvZ_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => fvZ η n B β h) := by
-- proof
  apply StatMech.Ising.meas_fvZ n B β h

/--
[meas_fvProb](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_fvProb_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
-- given
  (β h : ℝ)
  (τ : {x // x ∈ box d n} → Bool) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => fvProb η n B β h τ) := by
-- proof
  apply StatMech.Ising.meas_fvProb n B β h τ

/--
[meas_dirac_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_dirac_glue_eq
  {d : ℕ}
  {n : ℕ}
  {s : Set (ConfigSpace (Site d))}
-- given
  (τ : {x // x ∈ box d n} → Bool)
  (hs : MeasurableSet s) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => (Measure.dirac (glue η τ)) s) := by
-- proof
  apply StatMech.Ising.meas_dirac_glue n τ hs

/--
[meas_fvMeasure_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma meas_fvMeasure_coe_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {s : Set (ConfigSpace (Site d))}
-- given
  (β h : ℝ)
  (hs : MeasurableSet s) :
-- imply
  Measurable[outsideSigma (box d n)] (fun η : ConfigSpace (Site d) => (fvMeasure η n B β h) s) := by
-- proof
  apply StatMech.Ising.meas_fvMeasure_coe n B β h hs

/--
[isingSpec_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma isingSpec_apply_eq
  {d : ℕ}
  {n : ℕ}
  {B : Finset (Sym2 (Site d))}
  {η : ConfigSpace (Site d)}
-- given
  (β h : ℝ) :
-- imply
  (isingSpec n B β h) η = fvMeasure η n B β h := by
-- proof
  apply StatMech.Ising.isingSpec_apply n B β h η

/--
[gibbsConditional_ae_eq_isingSpec](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma gibbsConditional_ae_eq_isingSpec_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
  {n : ℕ}
-- given
  (β h : ℝ)
  (hμ : IsDLRState d β h μ) :
-- imply
  gibbsConditional μ (box d n) =ᵐ[μ] isingSpec n (bondFinsetTouch d n) β h := by
-- proof
  apply StatMech.Ising.gibbsConditional_ae_eq_isingSpec β h μ hμ n

/--
[dlr_compProd_trim_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma dlr_compProd_trim_eq_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
  {n : ℕ}
-- given
  (β h : ℝ)
  (hμ : IsDLRState d β h μ) :
-- imply
  (μ.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h) = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _ ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ := by
-- proof
  apply StatMech.Ising.dlr_compProd_trim_eq β h μ hμ n

/--
[isDLRState_of_compProd_trim](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma isDLRState_of_compProd_trim_eq
  {d : ℕ}
  {μ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ]
-- given
  (β h : ℝ)
  (hμ : ∀ n, (μ.trim (outsideSigma_le (box d n))) ⊗ₘ (isingSpec n (bondFinsetTouch d n) β h) = @Measure.map (ConfigSpace (Site d)) (ConfigSpace (Site d) × ConfigSpace (Site d)) _ ((outsideSigma (box d n)).prod inferInstance) (fun ω ↦ (id ω, id ω)) μ) :
-- imply
  IsDLRState d β h μ := by
-- proof
  apply StatMech.Ising.isDLRState_of_compProd_trim β h μ hμ

/--
[isDLRState_add_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma isDLRState_add_smul_eq
  {d : ℕ}
  {a b : ℝ≥0∞}
  {μ₁ μ₂ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ₁]
  [IsFiniteMeasure μ₂]
-- given
  (β h : ℝ)
  (hab : a + b = 1)
  (h₁ : IsDLRState d β h μ₁)
  (h₂ : IsDLRState d β h μ₂) :
-- imply
  haveI : IsFiniteMeasure (a • μ₁ + b • μ₂) := by
-- proof
  apply StatMech.Ising.isDLRState_add_smul β h hab μ₁ μ₂ h₁ h₂

/--
[convex_isDLRState](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GibbsSimplex.lean)
-/
@[path]
private lemma convex_isDLRState_eq
  {d : ℕ}
  {a b : ℝ≥0∞}
  {μ₁ μ₂ : Measure (ConfigSpace (Site d))}
  [IsFiniteMeasure μ₁]
  [IsFiniteMeasure μ₂]
  [IsFiniteMeasure (a • μ₁ + b • μ₂)]
-- given
  (β h : ℝ)
  (hab : a + b = 1)
  (h₁ : IsDLRState d β h μ₁)
  (h₂ : IsDLRState d β h μ₂) :
-- imply
  IsDLRState d β h (a • μ₁ + b • μ₂) := by
-- proof
  apply StatMech.Ising.convex_isDLRState β h hab μ₁ μ₂ h₁ h₂


-- created on 2026-10-23
