/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationClosedProp7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Localization.NormTrace
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic


noncomputable section

open PrimeSpectrum

namespace Proposition7

/-- The ramification locus of `A → B` (with `B` a free finite `A`-module) is
the zero locus of the discriminant; the closed set where the cover degenerates. -/
def ramificationLocus (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus {Algebra.discr A (Module.Free.chooseBasis A B)}

end Proposition7
end
