import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Exact3D.IsingRGCoordinateBridge
open StatMech StatMech.Exact3D StatMech.Exact3D.IsingRGCoordinateScaffold StatMech.Exact3D.IsingRGCoordinateBridgeInputs StatMech.Exact3D.IsingMassRGCoordinateScaffold StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs


/--
[mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C}
  {β : ℝ} :
-- imply
  β ∈ S.leftCriticalInterval ↔ β ∈ Set.Ioo (Ising.betaC 3 - S.δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.mem_leftCriticalInterval S

/--
[leftCriticalInterval_subset_Iio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma leftCriticalInterval_subset_Iio_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C} :
-- imply
  S.leftCriticalInterval ⊆ Set.Iio (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.leftCriticalInterval_subset_Iio S

/--
[betaC_sub_pos_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.betaC_sub_pos_of_mem_leftCriticalInterval S hβ

/--
[betaC_sub_lt_delta_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  Ising.betaC 3 - β < S.δ := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.betaC_sub_lt_delta_of_mem_leftCriticalInterval S hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ S.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.eventually_mem_leftCriticalInterval S

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.eventually_betaC_sub_pos S

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < S.δ := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.eventually_betaC_sub_lt_delta S

/--
[latticeRG_kernel_scale_eq_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma latticeRG_kernel_scale_eq_certificate_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C} :
-- imply
  S.latticeRG.kernel.scale = C.scale := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.latticeRG_kernel_scale_eq_certificate S

/--
[latticeRG_R_scale_eq_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma latticeRG_R_scale_eq_certificate_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C} :
-- imply
  S.latticeRG.R.scale = C.scale := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.latticeRG_R_scale_eq_certificate S

/--
[latticeRG_kernel_scale_toReal_eq_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma latticeRG_kernel_scale_toReal_eq_certificate_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C} :
-- imply
  S.latticeRG.kernel.scale.toReal = C.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.latticeRG_kernel_scale_toReal_eq_certificate S

/--
[latticeRG_R_scale_toReal_eq_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma latticeRG_R_scale_toReal_eq_certificate_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C} :
-- imply
  S.latticeRG.R.scale.toReal = C.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.latticeRG_R_scale_toReal_eq_certificate S

/--
[length_covariance_maps_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma length_covariance_maps_interval_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hcov : S.LengthCovariance)
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  S.renormalizedBeta β ∈ S.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.length_covariance_maps_interval S hcov hβ

/--
[length_covariance_lattice_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma length_covariance_lattice_scale_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hcov : S.LengthCovariance)
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  S.correlationLength (S.renormalizedBeta β) = S.correlationLength β / S.latticeRG.kernel.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.length_covariance_lattice_scale S hcov hβ

/--
[length_covariance_certificate_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma length_covariance_certificate_scale_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hcov : S.LengthCovariance)
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  S.correlationLength (S.renormalizedBeta β) = S.correlationLength β / C.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.length_covariance_certificate_scale S hcov hβ

/--
[coordinate_rg_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma coordinate_rg_covariance_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hcov : S.CoordinateRGCovariance)
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  C.R.map (S.coordinate β) = S.coordinate (S.renormalizedBeta β) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateScaffold.coordinate_rg_covariance S hcov hβ

/--
[length_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma length_scaling_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  T.scaffold.correlationLength β = T.scaffold.prefactor β * Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.length_scaling T hβ

/--
[renormalizedBeta_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma renormalizedBeta_mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.renormalizedBeta_mem_leftCriticalInterval T hβ

/--
[betaC_sub_renormalizedBeta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma betaC_sub_renormalizedBeta_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.betaC_sub_renormalizedBeta_pos T hβ

/--
[betaC_sub_renormalizedBeta_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma betaC_sub_renormalizedBeta_lt_delta_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.betaC_sub_renormalizedBeta_lt_delta T hβ

/--
[length_covariance_lattice_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma length_covariance_lattice_scale_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) = T.scaffold.correlationLength β / T.scaffold.latticeRG.kernel.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.length_covariance_lattice_scale T hβ

/--
[length_covariance_certificate_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma length_covariance_certificate_scale_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) = T.scaffold.correlationLength β / C.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.length_covariance_certificate_scale T hβ

/--
[renormalizedBeta_iterate_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma renormalizedBeta_iterate_mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  ∀ k : ℕ, (T.scaffold.renormalizedBeta^[k]) β ∈ T.scaffold.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.renormalizedBeta_iterate_mem_leftCriticalInterval T hβ

/--
[length_covariance_iterate_certificate_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma length_covariance_iterate_certificate_scale_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  ∀ k : ℕ, T.scaffold.correlationLength ((T.scaffold.renormalizedBeta^[k]) β) = T.scaffold.correlationLength β / (C.scale.toReal ^ k) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.length_covariance_iterate_certificate_scale T hβ

/--
[coordinate_rg_covariance_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma coordinate_rg_covariance_iterate_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  ∀ k : ℕ, ((C.R.map)^[k]) (T.scaffold.coordinate β) = T.scaffold.coordinate ((T.scaffold.renormalizedBeta^[k]) β) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.coordinate_rg_covariance_iterate T hβ

/--
[coordinate_rg_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma coordinate_rg_covariance_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  C.R.map (T.scaffold.coordinate β) = T.scaffold.coordinate (T.scaffold.renormalizedBeta β) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.coordinate_rg_covariance T hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ T.scaffold.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_mem_leftCriticalInterval T

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_betaC_sub_lt_delta T

/--
[eventually_coordinate_mem_rgNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_coordinate_mem_rgNeighborhood_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.coordinate β ∈ T.scaffold.rgNeighborhood := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_coordinate_mem_rgNeighborhood T

/--
[eventually_renormalizedBeta_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_renormalizedBeta_mem_leftCriticalInterval_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_renormalizedBeta_mem_leftCriticalInterval T

/--
[eventually_betaC_sub_renormalizedBeta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_renormalizedBeta_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_betaC_sub_renormalizedBeta_pos T

/--
[eventually_betaC_sub_renormalizedBeta_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_renormalizedBeta_lt_delta_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_betaC_sub_renormalizedBeta_lt_delta T

/--
[eventually_length_covariance_lattice_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_length_covariance_lattice_scale_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) = T.scaffold.correlationLength β / T.scaffold.latticeRG.kernel.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_length_covariance_lattice_scale T

/--
[eventually_length_covariance_certificate_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_length_covariance_certificate_scale_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.correlationLength (T.scaffold.renormalizedBeta β) = T.scaffold.correlationLength β / C.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_length_covariance_certificate_scale T

/--
[eventually_prefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_prefactor_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.scaffold.prefactor β := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_prefactor_pos T

/--
[eventually_length_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_length_scaling_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.correlationLength β = T.scaffold.prefactor β * Real.exp (-C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_length_scaling T

/--
[eventually_coordinate_rg_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_coordinate_rg_covariance_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), C.R.map (T.scaffold.coordinate β) = T.scaffold.coordinate (T.scaffold.renormalizedBeta β) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_coordinate_rg_covariance T

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.scaffold.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.hasCorrelationLength T hβ

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.scaffold.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_hasCorrelationLength T

/--
[toAnalyticPrefactorBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toAnalyticPrefactorBridgeInputs_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  RGCertificate.AnalyticPrefactorBridgeInputs C T.scaffold.correlationLength T.scaffold.prefactor (T.scaffold.LengthCovariance ∧ T.scaffold.CoordinateRGCovariance) T.stableManifoldControlStatement T.scaffold.MicroscopicOrbitEntry (∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.scaffold.correlationLength β)) where rgCovariance := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.toAnalyticPrefactorBridgeInputs T

/--
[toIsingAnalyticTarget_correlationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingAnalyticTarget_correlationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingAnalyticTarget.correlationLength = T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.toIsingAnalyticTarget_correlationLength T

/--
[toIsingAnalyticTarget_prefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingAnalyticTarget_prefactor_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingAnalyticTarget.prefactor = T.scaffold.prefactor := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.toIsingAnalyticTarget_prefactor T

/--
[toIsingAnalyticTarget_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingAnalyticTarget_delta_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingAnalyticTarget.δ = T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.toIsingAnalyticTarget_delta T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  C.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.rgToExponentBridge T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCriticalNu_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.hasCriticalNu T

/--
[eventually_correlationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.correlationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.eventually_correlationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma valid_of_checks_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.hasCriticalNu_congr_predictedExponent hpred T

/--
[rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent hpred T

/--
[hasCriticalNu_liminfCorrelationLength_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.hasCriticalNu_liminfCorrelationLength_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_congr_predictedExponent_eq
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingRGCoordinateBridgeInputs.valid_of_checks_liminfCorrelationLength_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C}
  {β : ℝ} :
-- imply
  β ∈ S.leftCriticalInterval ↔ β ∈ Set.Ioo (Ising.betaC 3 - S.δ) (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.mem_leftCriticalInterval S

/--
[leftCriticalInterval_subset_Iio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma leftCriticalInterval_subset_Iio_eq_2
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C} :
-- imply
  S.leftCriticalInterval ⊆ Set.Iio (Ising.betaC 3) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.leftCriticalInterval_subset_Iio S

/--
[betaC_sub_pos_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma betaC_sub_pos_of_mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.betaC_sub_pos_of_mem_leftCriticalInterval S hβ

/--
[betaC_sub_lt_delta_of_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma betaC_sub_lt_delta_of_mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  Ising.betaC 3 - β < S.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.betaC_sub_lt_delta_of_mem_leftCriticalInterval S hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq_3
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ S.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.eventually_mem_leftCriticalInterval S

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_3
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.eventually_betaC_sub_pos S

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_3
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < S.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.eventually_betaC_sub_lt_delta S

/--
[latticeRG_kernel_scale_eq_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma latticeRG_kernel_scale_eq_certificate_eq_2
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C} :
-- imply
  S.latticeRG.kernel.scale = C.scale := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.latticeRG_kernel_scale_eq_certificate S

/--
[latticeRG_R_scale_eq_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma latticeRG_R_scale_eq_certificate_eq_2
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C} :
-- imply
  S.latticeRG.R.scale = C.scale := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.latticeRG_R_scale_eq_certificate S

/--
[latticeRG_kernel_scale_toReal_eq_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma latticeRG_kernel_scale_toReal_eq_certificate_eq_2
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C} :
-- imply
  S.latticeRG.kernel.scale.toReal = C.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.latticeRG_kernel_scale_toReal_eq_certificate S

/--
[latticeRG_R_scale_toReal_eq_certificate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma latticeRG_R_scale_toReal_eq_certificate_eq_2
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C} :
-- imply
  S.latticeRG.R.scale.toReal = C.scale.toReal := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.latticeRG_R_scale_toReal_eq_certificate S

/--
[mass_covariance_maps_interval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma mass_covariance_maps_interval_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hcov : S.MassCovariance)
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  S.renormalizedBeta β ∈ S.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.mass_covariance_maps_interval S hcov hβ

/--
[mass_covariance_lattice_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma mass_covariance_lattice_scale_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hcov : S.MassCovariance)
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  S.mass (S.renormalizedBeta β) = S.latticeRG.kernel.scale.toReal * S.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.mass_covariance_lattice_scale S hcov hβ

/--
[mass_covariance_certificate_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma mass_covariance_certificate_scale_eq
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hcov : S.MassCovariance)
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  S.mass (S.renormalizedBeta β) = C.scale.toReal * S.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.mass_covariance_certificate_scale S hcov hβ

/--
[coordinate_rg_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma coordinate_rg_covariance_eq_3
  {C : RGCertificate Ising3DModel}
  {S : IsingMassRGCoordinateScaffold C}
  {β : ℝ}
-- given
  (hcov : S.CoordinateRGCovariance)
  (hβ : β ∈ S.leftCriticalInterval) :
-- imply
  C.R.map (S.coordinate β) = S.coordinate (S.renormalizedBeta β) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateScaffold.coordinate_rg_covariance S hcov hβ

/--
[mass_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma mass_scaling_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  T.scaffold.mass β = T.scaffold.massPrefactor β * Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.mass_scaling T hβ

/--
[renormalizedBeta_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma renormalizedBeta_mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.renormalizedBeta_mem_leftCriticalInterval T hβ

/--
[betaC_sub_renormalizedBeta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma betaC_sub_renormalizedBeta_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.betaC_sub_renormalizedBeta_pos T hβ

/--
[betaC_sub_renormalizedBeta_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma betaC_sub_renormalizedBeta_lt_delta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.betaC_sub_renormalizedBeta_lt_delta T hβ

/--
[mass_covariance_lattice_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma mass_covariance_lattice_scale_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  T.scaffold.mass (T.scaffold.renormalizedBeta β) = T.scaffold.latticeRG.kernel.scale.toReal * T.scaffold.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.mass_covariance_lattice_scale T hβ

/--
[mass_covariance_certificate_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma mass_covariance_certificate_scale_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  T.scaffold.mass (T.scaffold.renormalizedBeta β) = C.scale.toReal * T.scaffold.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.mass_covariance_certificate_scale T hβ

/--
[renormalizedBeta_iterate_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma renormalizedBeta_iterate_mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  ∀ k : ℕ, (T.scaffold.renormalizedBeta^[k]) β ∈ T.scaffold.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.renormalizedBeta_iterate_mem_leftCriticalInterval T hβ

/--
[mass_covariance_iterate_certificate_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma mass_covariance_iterate_certificate_scale_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  ∀ k : ℕ, T.scaffold.mass ((T.scaffold.renormalizedBeta^[k]) β) = (C.scale.toReal ^ k) * T.scaffold.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.mass_covariance_iterate_certificate_scale T hβ

/--
[coordinate_rg_covariance_iterate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma coordinate_rg_covariance_iterate_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  ∀ k : ℕ, ((C.R.map)^[k]) (T.scaffold.coordinate β) = T.scaffold.coordinate ((T.scaffold.renormalizedBeta^[k]) β) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.coordinate_rg_covariance_iterate T hβ

/--
[coordinate_rg_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma coordinate_rg_covariance_eq_4
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  C.R.map (T.scaffold.coordinate β) = T.scaffold.coordinate (T.scaffold.renormalizedBeta β) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.coordinate_rg_covariance T hβ

/--
[eventually_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_mem_leftCriticalInterval_eq_4
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), β ∈ T.scaffold.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_mem_leftCriticalInterval T

/--
[eventually_betaC_sub_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_pos_eq_4
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_betaC_sub_pos T

/--
[eventually_betaC_sub_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_lt_delta_eq_4
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - β < T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_betaC_sub_lt_delta T

/--
[eventually_coordinate_mem_rgNeighborhood](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_coordinate_mem_rgNeighborhood_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.coordinate β ∈ T.scaffold.rgNeighborhood := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_coordinate_mem_rgNeighborhood T

/--
[eventually_renormalizedBeta_mem_leftCriticalInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_renormalizedBeta_mem_leftCriticalInterval_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.renormalizedBeta β ∈ T.scaffold.leftCriticalInterval := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_renormalizedBeta_mem_leftCriticalInterval T

/--
[eventually_betaC_sub_renormalizedBeta_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_renormalizedBeta_pos_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < Ising.betaC 3 - T.scaffold.renormalizedBeta β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_betaC_sub_renormalizedBeta_pos T

/--
[eventually_betaC_sub_renormalizedBeta_lt_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_betaC_sub_renormalizedBeta_lt_delta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), Ising.betaC 3 - T.scaffold.renormalizedBeta β < T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_betaC_sub_renormalizedBeta_lt_delta T

/--
[eventually_mass_covariance_lattice_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_mass_covariance_lattice_scale_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.mass (T.scaffold.renormalizedBeta β) = T.scaffold.latticeRG.kernel.scale.toReal * T.scaffold.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_mass_covariance_lattice_scale T

/--
[eventually_mass_covariance_certificate_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_mass_covariance_certificate_scale_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.mass (T.scaffold.renormalizedBeta β) = C.scale.toReal * T.scaffold.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_mass_covariance_certificate_scale T

/--
[eventually_mass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_mass_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.scaffold.mass β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_mass_pos T

/--
[eventually_massPrefactor_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_massPrefactor_pos_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), 0 < T.scaffold.massPrefactor β := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_massPrefactor_pos T

/--
[eventually_mass_scaling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_mass_scaling_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.mass β = T.scaffold.massPrefactor β * Real.exp (C.predictedExponent * Real.log (Ising.betaC 3 - β)) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_mass_scaling T

/--
[eventually_correlationLength_eq_inv_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_inv_mass_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.correlationLength β = (T.scaffold.mass β)⁻¹ := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_correlationLength_eq_inv_mass T

/--
[eventually_coordinate_rg_covariance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_coordinate_rg_covariance_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), C.R.map (T.scaffold.coordinate β) = T.scaffold.coordinate (T.scaffold.renormalizedBeta β) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_coordinate_rg_covariance T

/--
[hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasInverseCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.scaffold.mass β) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.hasInverseCorrelationLength T hβ

/--
[eventually_hasInverseCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_hasInverseCorrelationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.scaffold.mass β) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_hasInverseCorrelationLength T

/--
[hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
  {β : ℝ}
-- given
  (hβ : β ∈ T.scaffold.leftCriticalInterval) :
-- imply
  HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.scaffold.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.hasCorrelationLength T hβ

/--
[eventually_hasCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_hasCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.scaffold.correlationLength β) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_hasCorrelationLength T

/--
[toAnalyticMassBridgeInputs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toAnalyticMassBridgeInputs_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  RGCertificate.AnalyticMassBridgeInputs C T.scaffold.correlationLength T.scaffold.mass T.scaffold.massPrefactor (T.scaffold.MassCovariance ∧ T.scaffold.CoordinateRGCovariance) T.stableManifoldControlStatement T.scaffold.MicroscopicOrbitEntry (∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), HasInverseCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay (T.scaffold.mass β)) where rgCovariance := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toAnalyticMassBridgeInputs T

/--
[toIsingMassPowerLawTarget_correlationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassPowerLawTarget_correlationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassPowerLawTarget.correlationLength = T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassPowerLawTarget_correlationLength T

/--
[toIsingMassPowerLawTarget_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassPowerLawTarget_mass_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassPowerLawTarget.mass = T.scaffold.mass := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassPowerLawTarget_mass T

/--
[toIsingMassPowerLawTarget_massPrefactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassPowerLawTarget_massPrefactor_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassPowerLawTarget.massPrefactor = T.scaffold.massPrefactor := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassPowerLawTarget_massPrefactor T

/--
[toIsingMassPowerLawTarget_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassPowerLawTarget_delta_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassPowerLawTarget.δ = T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassPowerLawTarget_delta T

/--
[toIsingMassPowerLawTarget_toIsingMassTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassPowerLawTarget_toIsingMassTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassPowerLawTarget.toMassTarget = T.toIsingMassTarget := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassPowerLawTarget_toIsingMassTarget T

/--
[toIsingMassTarget_toIsingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassTarget_toIsingAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassTarget.toLengthTarget = T.toIsingAnalyticTarget := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassTarget_toIsingAnalyticTarget T

/--
[toIsingMassPowerLawTarget_toIsingAnalyticTarget](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassPowerLawTarget_toIsingAnalyticTarget_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassPowerLawTarget.toLengthTarget = T.toIsingAnalyticTarget := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassPowerLawTarget_toIsingAnalyticTarget T

/--
[toIsingMassTarget_correlationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassTarget_correlationLength_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassTarget.correlationLength = T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassTarget_correlationLength T

/--
[toIsingMassTarget_mass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassTarget_mass_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassTarget.mass = T.scaffold.mass := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassTarget_mass T

/--
[toIsingMassTarget_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingMassTarget_delta_eq
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingMassTarget.δ = T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingMassTarget_delta T

/--
[toIsingAnalyticTarget_correlationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingAnalyticTarget_correlationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingAnalyticTarget.correlationLength = T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingAnalyticTarget_correlationLength T

/--
[toIsingAnalyticTarget_delta](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma toIsingAnalyticTarget_delta_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  T.toIsingAnalyticTarget.δ = T.scaffold.δ := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.toIsingAnalyticTarget_delta T

/--
[rgToExponentBridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  C.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.rgToExponentBridge T

/--
[hasCriticalNu](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCriticalNu_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.hasCriticalNu T

/--
[eventually_correlationLength_eq_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma eventually_correlationLength_eq_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  ∀ᶠ β in nhdsWithin (Ising.betaC 3) (Set.Iio (Ising.betaC 3)), T.scaffold.correlationLength β = liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.eventually_correlationLength_eq_liminfCorrelationLength T

/--
[rgToExponentBridge_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  C.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.rgToExponentBridge_liminfCorrelationLength T

/--
[hasCriticalNu_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C} :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) C.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.hasCriticalNu_liminfCorrelationLength T

/--
[valid_of_checks](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma valid_of_checks_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.valid_of_checks T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_eq_2
  {C : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hfinite : C.FiniteCaseChecks)
  (htail : C.TailBounds)
  (hfixed : C.FixedPointEnclosure)
  (hlinear : C.LinearizationEnclosure)
  (hhyperbolic : C.HyperbolicSplitting)
  (horbit : C.OrbitEntry) :
-- imply
  C.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.valid_of_checks_liminfCorrelationLength T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[rgToExponentBridge_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.rgToExponentBridge_congr_predictedExponent hpred T

/--
[hasCriticalNu_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCriticalNu_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel T.scaffold.correlationLength D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.hasCriticalNu_congr_predictedExponent hpred T

/--
[rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  D.RGToExponentBridge (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.rgToExponentBridge_liminfCorrelationLength_congr_predictedExponent hpred T

/--
[hasCriticalNu_liminfCorrelationLength_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma hasCriticalNu_liminfCorrelationLength_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent) :
-- imply
  HasCriticalNu Ising3DModel (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) D.predictedExponent := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.hasCriticalNu_liminfCorrelationLength_congr_predictedExponent hpred T

/--
[valid_of_checks_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma valid_of_checks_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid T.scaffold.correlationLength := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.valid_of_checks_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit

/--
[valid_of_checks_liminfCorrelationLength_congr_predictedExponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/IsingRGCoordinateBridge.lean)
-/
@[path]
private lemma valid_of_checks_liminfCorrelationLength_congr_predictedExponent_eq_2
  {C : RGCertificate Ising3DModel}
  {D : RGCertificate Ising3DModel}
  {T : IsingMassRGCoordinateBridgeInputs C}
-- given
  (hpred : D.predictedExponent = C.predictedExponent)
  (hfinite : D.FiniteCaseChecks)
  (htail : D.TailBounds)
  (hfixed : D.FixedPointEnclosure)
  (hlinear : D.LinearizationEnclosure)
  (hhyperbolic : D.HyperbolicSplitting)
  (horbit : D.OrbitEntry) :
-- imply
  D.Valid (fun β : ℝ => liminfCorrelationLength Ising3DModel β ising3DOrigin ising3DXAxisRay) := by
-- proof
  apply StatMech.Exact3D.IsingMassRGCoordinateBridgeInputs.valid_of_checks_liminfCorrelationLength_congr_predictedExponent hpred T hfinite htail hfixed hlinear hhyperbolic horbit


-- created on 2026-10-23
