/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/NilpotentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Rank
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Basic
import Mathlib.Topology.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Structure.v1.Atlas.LieGroups.code.NilpotentCone.Part2


noncomputable section

open scoped LieAlgebra

open Set

namespace LieAlgebra

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable {R L}

variable [Module.Finite R L] [Module.Free R L]

section PrincipalSl2

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]

def BorelSubgroupData.regularNilpotentSet {rsd : RootSystemData 𝔤}
    (BD : BorelSubgroupData 𝔤 rsd) : Set 𝔤 :=
  { x : 𝔤 | ∃ (c : Fin BD.numPosRoots → ℂ),
      (∀ i, BD.isSimple i → c i ≠ 0) ∧
      x = ∑ i, c i • BD.rootVector i }

def BorelSubgroupData.borelOrbit {rsd : RootSystemData 𝔤}
    (BD : BorelSubgroupData 𝔤 rsd) (e : 𝔤) : Set 𝔤 :=
  { y : 𝔤 | ∃ b : BD.B, @BD.AdB b e = y }

end PrincipalSl2
end LieAlgebra
end
