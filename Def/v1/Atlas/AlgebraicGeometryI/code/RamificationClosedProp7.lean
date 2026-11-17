/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RamificationClosedProp7.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.Discriminant
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

@[expose] public section

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
