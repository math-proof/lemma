/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CoherentSpecFinitelyGenerated.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.Algebra.Module.LocalizedModule.Basic

namespace CoherentSpecFinitelyGenerated

/-- An `R`-module `M` is locally finitely generated if there exists a finite set of elements
of `R` generating the unit ideal such that each corresponding localization of `M` is finitely
generated. -/
def IsLocallyFinitelyGenerated
    (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M] : Prop :=
  ∃ (s : Finset R), Ideal.span (s : Set R) = ⊤ ∧
    ∀ (r : s), Module.Finite (Localization.Away r.val)
      (LocalizedModule (Submonoid.powers r.val) M)
