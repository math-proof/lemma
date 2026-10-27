import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryApproximation.Part3
open Filter Set Topology Metric StatMech StatMech.Universality StatMech.Universality.FKIsingCaratheodoryApproximation


/--
[normalizedInterpolant_medial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean)
-/
@[path]
private lemma normalizedInterpolant_medial_eq
  {A : FKIsingCaratheodoryApproximation}
  {n : Nat}
  {e : A.M n} :
-- imply
  A.normalizedInterpolant n (A.medialEmbedding n e) = @FKIsingDobrushinDomain.normalizedFermionicObservable (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.normalizedInterpolant_medial A n e

/--
[compact_eventually_near_medial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean)
-/
@[path]
private lemma compact_eventually_near_medial_eq
  {A : FKIsingCaratheodoryApproximation}
  {K : Set Complex}
-- given
  (hKcompact : IsCompact K)
  (hKU : K ⊆ A.U) :
-- imply
  ∀ᶠ n in atTop, ∀ z ∈ K, ∃ e : A.M n, dist z (A.medialEmbedding n e) ≤ A.mesh n := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.compact_eventually_near_medial A K hKcompact hKU

/--
[exists_normalizedObservable_near](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean)
-/
@[path]
private lemma exists_normalizedObservable_near_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.HolderInterpolation}
  {n : Nat}
  {z : Complex}
-- given
  (hz : z ∈ A.carrier n) :
-- imply
  ∃ e : A.M n, dist (A.normalizedInterpolant n z) (@FKIsingDobrushinDomain.normalizedFermionicObservable (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e) ≤ I.constant * A.mesh n ^ (I.exponent : Real) := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.exists_normalizedObservable_near A I n z hz

/--
[holderInterpolation_error_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean)
-/
@[path]
private lemma holderInterpolation_error_tendsto_zero_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.HolderInterpolation} :
-- imply
  Tendsto (fun n ↦ (I.constant : Real) * A.mesh n ^ (I.exponent : Real)) atTop (nhds 0) := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.holderInterpolation_error_tendsto_zero A I

/--
[compactBounds_of_holderInterpolation_and_eventualMedialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean)
-/
@[path]
private lemma compactBounds_of_holderInterpolation_and_eventualMedialBounds_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.HolderInterpolation}
  {I : A.HolderInterpolation}
-- given
  (hhol : ∀ n, DifferentiableOn Complex (A.normalizedInterpolant n) A.U)
  (hmedial : ∀ K : Set Complex, IsCompact K → K ⊆ A.U → ∃ B : Real, ∀ᶠ n in atTop, ∀ e : A.M n, (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) → ‖@FKIsingDobrushinDomain.normalizedFermionicObservable (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤ B) :
-- imply
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U → ∃ C : Real, ∀ n z, z ∈ K → ‖A.normalizedInterpolant n z‖ ≤ C := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.compactBounds_of_holderInterpolation_and_eventualMedialBounds A I I hhol hmedial

/--
[compactBounds_of_holderInterpolation_and_medialBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean)
-/
@[path]
private lemma compactBounds_of_holderInterpolation_and_medialBounds_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.HolderInterpolation}
  {I : A.HolderInterpolation}
-- given
  (hhol : ∀ n, DifferentiableOn Complex (A.normalizedInterpolant n) A.U)
  (hmedial : ∀ K : Set Complex, IsCompact K → K ⊆ A.U → ∃ B : Real, ∀ n (e : A.M n), (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) → ‖@FKIsingDobrushinDomain.normalizedFermionicObservable (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤ B) :
-- imply
  ∀ K : Set Complex, IsCompact K → K ⊆ A.U → ∃ C : Real, ∀ n z, z ∈ K → ‖A.normalizedInterpolant n z‖ ≤ C := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.compactBounds_of_holderInterpolation_and_medialBounds A I I hhol hmedial

/--
[scalingLimit_of_holderMedialBounds_and_primitiveIm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean)
-/
@[path]
private lemma scalingLimit_of_holderMedialBounds_and_primitiveIm_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.HolderInterpolation}
  {I : A.HolderInterpolation}
  {target Phi : Complex → Complex}
  {E : StatMech.FrontierA.CompactExhaustion A.U}
-- given
  (hhol : ∀ n, DifferentiableOn Complex (A.normalizedInterpolant n) A.U)
  (htarget : DifferentiableOn Complex target A.U)
  (htarget_ne : target A.root ≠ 0)
  (hPhi : DifferentiableOn Complex Phi A.U)
  (hPhideriv : Set.EqOn (deriv Phi) (fun z ↦ target z ^ 2) A.U)
  (hmedial : ∀ K : Set Complex, IsCompact K → K ⊆ A.U → ∃ B : Real, ∀ n (e : A.M n), (∃ z ∈ K, dist z (A.medialEmbedding n e) ≤ A.mesh n) → ‖@FKIsingDobrushinDomain.normalizedFermionicObservable (A.P n) (A.M n) (A.decEqM n) (A.dobrushin n) (A.mesh n) e‖ ≤ B)
  (hidentifyPrimitive : ∀ (phi psi : Nat → Nat) (f : Complex → Complex), StrictMono phi → StrictMono psi → TendstoLocallyUniformlyOn (fun n ↦ A.normalizedInterpolant (phi (psi n))) f atTop A.U → ∃ (P : Complex → Complex) (C : Real), DifferentiableOn Complex P A.U ∧ Set.EqOn (deriv P) (fun z ↦ f z ^ 2) A.U ∧ (∀ z ∈ A.U, (P z).im = (Phi z).im + C) ∧ f A.root = target A.root) :
-- imply
  TendstoLocallyUniformlyOn A.normalizedInterpolant target atTop A.U ∧ TendstoLocallyUniformlyOn (deriv ∘ A.normalizedInterpolant) (deriv target) atTop A.U := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.scalingLimit_of_holderMedialBounds_and_primitiveIm A I I target Phi hhol htarget htarget_ne hPhi hPhideriv E hmedial hidentifyPrimitive

/--
[boundary_error_le_mesh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean)
-/
@[path]
private lemma boundary_error_le_mesh_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.HolderInterpolation}
  {B : A.BoundarySampling}
  {n : Nat}
  {v : (A.P n).V}
-- given
  (hv : B.boundary n v) :
-- imply
  |B.discreteDatum n v - (B.Phi (A.vertexEmbedding n v)).im| ≤ B.lipschitzConstant * A.mesh n := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.boundary_error_le_mesh A I B n v hv

/--
[boundary_data_tendsto_uniformly](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicCaratheodoryApproximation.lean)
-/
@[path]
private lemma boundary_data_tendsto_uniformly_eq
  {A : FKIsingCaratheodoryApproximation}
  {I : A.HolderInterpolation}
  {B : A.BoundarySampling} :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ v, B.boundary n v → |B.discreteDatum n v - (B.Phi (A.vertexEmbedding n v)).im| < eta := by
-- proof
  apply StatMech.Universality.FKIsingCaratheodoryApproximation.boundary_data_tendsto_uniformly A I B


-- created on 2026-10-23
