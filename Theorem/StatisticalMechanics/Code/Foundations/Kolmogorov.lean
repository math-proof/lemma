/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Kolmogorov.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Instance.StatisticalMechanics.Code.Foundations.Kolmogorov
open MeasureTheory


namespace StatMech

namespace Kolmogorov

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
  (μ : (i : ι) → Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)]


theorem extension_isProbabilityMeasure : IsProbabilityMeasure (extension μ) :=
  isProbabilityMeasure μ


theorem extension_isProjectiveLimit :
    IsProjectiveLimit (extension μ) (fun I : Finset ι => Measure.pi (fun i : I => μ i)) :=
  Measure.isProjectiveLimit_infinitePi μ


theorem extension_map_restrict (I : Finset ι) :
    (extension μ).map I.restrict = Measure.pi (fun i : I => μ i) :=
  Measure.isProjectiveLimit_infinitePi μ I


theorem extension_cylinder {I : Finset ι} {S : Set (Π i : I, X i)} (hS : MeasurableSet S) :
    extension μ (cylinder I S) = Measure.pi (fun i : I => μ i) S :=
  Measure.infinitePi_cylinder μ hS


theorem extension_pi {s : Finset ι} {t : (i : ι) → Set (X i)}
    (ht : ∀ i ∈ s, MeasurableSet (t i)) :
    extension μ (Set.pi s t) = ∏ i ∈ s, μ i (t i) :=
  Measure.infinitePi_pi μ ht


theorem extension_unique {ν : Measure (Π i, X i)}
    (hν : ∀ (s : Finset ι) (t : (i : ι) → Set (X i)),
      (∀ i, MeasurableSet (t i)) → ν (Set.pi s t) = ∏ i ∈ s, μ i (t i)) :
    ν = extension μ :=
  Measure.eq_infinitePi μ hν


theorem extension_unique_of_isProjectiveLimit {ν : Measure (Π i, X i)}
    (hν : IsProjectiveLimit ν (fun I : Finset ι => Measure.pi (fun i : I => μ i))) :
    ν = extension μ :=
  hν.unique (extension_isProjectiveLimit μ)

end Kolmogorov
end StatMech
