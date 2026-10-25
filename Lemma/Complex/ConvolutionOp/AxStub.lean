import Mathlib
import sympy.atlas.v1.Atlas.LieGroups.code.PlancherelCompact
open MeasureTheory PlancherelCompact
open scoped Topology Manifold

axiom ax_concreteDiracEmbed_apply_eq_
  [TopologicalSpace X]
  {σ : Finsupp X ℂ}
  {f : ContMapComplex X} :
  (concreteDiracEmbed X σ) f = ∑ x ∈ σ.support, σ x * f x

axiom ax_finitely_supported_seq_dense_in_measures
  [TopologicalSpace X]
  [LocallyCompactSpace X]
  [SecondCountableTopology X]
  [T2Space X]
  {μ : ContMapComplex X →L[ℂ] ℂ} :
  ∃ (μ_seq : ℕ → (ContMapComplex X) →L[ℂ] ℂ), (∀ n, ∃ (S : Finset X) (c : X → ℂ), ∀ (f : ContMapComplex X), μ_seq n f = ∑ x ∈ S, c x * f x) ∧ (∀ (f : ContMapComplex X), Filter.Tendsto (fun n => μ_seq n f) Filter.atTop (nhds (μ f)))

axiom ax_compactly_supported_measure_to_clm
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [T2Space G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]
-- given
  (hμ : IsCompact μ.support) :
  ∃ (Φ : ContMapComplex G →L[ℂ] ℂ), ∀ (f : ContMapComplex G), Φ f = ∫ (g : G), f g ∂μ

axiom ax_cc_seq_dense_approx_finsupp
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [T2Space G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  {μ : Measure G}
  [IsFiniteMeasureOnCompacts μ]
-- given
  (hμ : IsCompact μ.support) :
  ∃ (S : ℕ → Finset G) (c : ℕ → G → ℂ), ∀ (f : G → ℂ), Continuous f → Filter.Tendsto (fun n => ∑ x ∈ S n, c n x * f x) Filter.atTop (nhds (∫ (g : G), f g ∂μ))

axiom ax_derivedRep_preserves_smooth
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup EG]
  [NormedSpace ℝ EG]
  [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [LieGroup IG ⊤ G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [CompleteSpace F]
  {π : ContinuousRep G F}
  {lieExp : EG → G}
  {b : EG}
  {v : F}
-- given
  (hExp : ContMDiff (modelWithCornersSelf ℝ EG) IG ⊤ lieExp)
  (hExp1 : lieExp 0 = 1)
  (hv : π.IsSmoothVector IG v) :
  π.IsSmoothVector IG (π.derivedRep lieExp b v)

axiom ax_kfinite_subset_smooth
  [Group G]
  [TopologicalSpace G]
  [NormedAddCommGroup EG]
  [NormedSpace ℝ EG]
  [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [LieGroup IG ⊤ G]
  [NormedAddCommGroup F]
  [NormedSpace ℂ F]
  [CompleteSpace F]
  {π : ContinuousRep G F}
  {v : F}
-- given
  (hv : ContinuousRep.IsKFinite π ⊤ v) :
  π.IsSmoothVector IG v

axiom ax_exists_smooth_dirac_sequence
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  [NormedAddCommGroup EG]
  [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG]
  [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [LieGroup IG ⊤ G]
  [T2Space G] :
  ∃ (φ : ℕ → G → ℝ), (∀ (n : ℕ), ContMDiff IG (modelWithCornersSelf ℝ ℝ) (⊤ : WithTop (WithTop ℕ)) (φ n)) ∧ (∀ (n : ℕ), HasCompactSupport (φ n)) ∧ (∀ (f : G → ℂ), Continuous f → HasCompactSupport f → Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (φ n g : ℂ) * f g) Filter.atTop (nhds (f 1)))

axiom ax_smooth_cc_seq_converges_to_dirac
  [Group G]
  [TopologicalSpace G]
  [IsTopologicalGroup G]
  [LocallyCompactSpace G]
  [SecondCountableTopology G]
  [MeasureSpace G]
  [BorelSpace G]
  [Measure.IsHaarMeasure (volume : Measure G)]
  [NormedAddCommGroup EG]
  [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG]
  [TopologicalSpace HG]
  {IG : ModelWithCorners ℝ EG HG}
  [ChartedSpace HG G]
  [LieGroup IG ⊤ G]
  [T2Space G]
  {g₀ : G} :
  ∃ (ψ : ℕ → G → ℝ), (∀ (n : ℕ), ContMDiff IG (modelWithCornersSelf ℝ ℝ) (⊤ : WithTop (WithTop ℕ)) (ψ n)) ∧ (∀ (n : ℕ), HasCompactSupport (ψ n)) ∧ (∀ (f : G → ℂ), Continuous f → HasCompactSupport f → Filter.Tendsto (fun (n : ℕ) => ∫ (g : G), (ψ n g : ℂ) * f g) Filter.atTop (nhds (f g₀)))

