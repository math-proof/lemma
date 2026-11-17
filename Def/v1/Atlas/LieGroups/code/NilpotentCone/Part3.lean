/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/NilpotentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Semisimple.Basic
public import Mathlib.Algebra.Lie.CartanSubalgebra
public import Mathlib.Algebra.Lie.Sl2
public import Mathlib.Algebra.Lie.Rank
public import Mathlib.Algebra.Lie.CartanExists
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Lie.UniversalEnveloping
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Irreducible
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Structure.v1.Atlas.LieGroups.code.NilpotentCone.Part2

@[expose] public section

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
