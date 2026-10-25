/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Abbrev.v1.Atlas.GeometryOfManifolds.code.HodgeTheory
set_option autoImplicit false

open DifferentialFormSpace


/-- The space $\mathcal{H}^{p+1} = \{\alpha \in \Omega^{p+1} : \Delta \alpha = 0\}$
of harmonic forms of degree $p+1$. -/
def HarmonicForms {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : Codifferential (inst := inst)) (p : ℕ) : Set (Ω (p + 1)) :=
  {α | IsHarmonic cod α}


