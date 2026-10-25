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
import Structure.v1.Atlas.LieGroups.code.NilpotentCone


noncomputable section

open scoped LieAlgebra

open Set

namespace LieAlgebra

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable {R L}

def AdjointOrbit (Gact : AdjointGroupAction R L) (x : L) : Set L :=
  { y : L | ∃ g : Gact.G, Gact.Ad g x = y }

def IsAdjointConjugate (Gact : AdjointGroupAction R L) (x y : L) : Prop :=
  ∃ g : Gact.G, Gact.Ad g x = y

def lieCentralizer (x : L) : Submodule R L :=
  LinearMap.ker (LieAlgebra.ad R L x : L →ₗ[R] L)

variable [Module.Finite R L] [Module.Free R L]

def IsRegularElement (x : L) : Prop :=
  Module.finrank R (lieCentralizer R L x) = LieAlgebra.rank R L

def IsRegularNilpotent (x : L) : Prop :=
  IsNilpotentElement R L x ∧ IsRegularElement R L x

section PrincipalSl2

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]

def IsAdInvariant (x : 𝔤) (V : Submodule ℂ 𝔤) : Prop :=
  ∀ v ∈ V, (LieAlgebra.ad ℂ 𝔤 x) v ∈ V

def IsSl2SubmoduleOf (h e f : 𝔤) (V : Submodule ℂ 𝔤) : Prop :=
  IsAdInvariant h V ∧ IsAdInvariant e V ∧ IsAdInvariant f V

def IsSl2IrreducibleSubmoduleOf (h e f : 𝔤) (V : Submodule ℂ 𝔤) : Prop :=
  V ≠ ⊥ ∧ IsSl2SubmoduleOf h e f V ∧
  ∀ W : Submodule ℂ 𝔤, W ≤ V → IsSl2SubmoduleOf h e f W → W = ⊥ ∨ W = V

def IsSl2SubmoduleOf.toLieSubmodule {h e f : 𝔤} (t : IsSl2Triple h e f)
    {V : Submodule ℂ 𝔤} (hV : IsSl2SubmoduleOf h e f V) :
    LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤 where
  __ := V
  lie_mem {x v} hv := by
    obtain ⟨c₁, c₂, c₃, hx⟩ := IsSl2Triple.mem_toLieSubalgebra_iff.mp x.2
    have hv_h := hV.1 v hv
    have hv_e := hV.2.1 v hv
    have hv_f := hV.2.2 v hv

    have heq : ⁅(x : 𝔤), v⁆ = c₁ • ⁅e, v⁆ + c₂ • ⁅f, v⁆ + c₃ • ⁅h, v⁆ := by
      rw [hx, add_lie, add_lie, smul_lie, smul_lie, smul_lie, t.lie_e_f]
    show ⁅(x : 𝔤), v⁆ ∈ V
    rw [heq]
    exact V.add_mem (V.add_mem (V.smul_mem _ hv_e) (V.smul_mem _ hv_f)) (V.smul_mem _ hv_h)

def IsSl2IrreducibleLieSubmodule {h e f : 𝔤} (t : IsSl2Triple h e f)
    (V : LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤) : Prop :=
  V ≠ ⊥ ∧
  ∀ W : LieSubmodule ℂ (↥(t.toLieSubalgebra ℂ)) 𝔤,
    W.toSubmodule ≤ V.toSubmodule → W = ⊥ ∨ W = V

end PrincipalSl2
end LieAlgebra
end
