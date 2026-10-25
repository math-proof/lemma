/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec9Blowups.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.ReesAlgebra
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Def.v1.Atlas.AlgebraicGeometryI.code.Lec9Blowups
open Polynomial


namespace Lec9Blowups

/-- A polynomial lies in the blowup algebra of `𝔪` iff each of its
coefficients lies in the corresponding power of `𝔪`. -/
theorem mem_blowupAlgebra_iff {A : Type*} [CommRing A] {𝔪 : Ideal A}
    (f : A[X]) :
    f ∈ blowupAlgebra A 𝔪 ↔ ∀ i, f.coeff i ∈ 𝔪 ^ i :=
  mem_reesAlgebra_iff (I := 𝔪) f

/-- A ring map `φ : R → A` carries the blowup algebra of `φ⁻¹(𝔪)` into
the blowup algebra of `𝔪`. -/
theorem map_mem_blowupAlgebra {R A : Type*} [CommRing R] [CommRing A]
    (φ : R →+* A) (𝔪 : Ideal A) (f : R[X]) (hf : f ∈ blowupAlgebra R (𝔪.comap φ)) :
    f.map φ ∈ blowupAlgebra A 𝔪 := by
  rw [mem_blowupAlgebra_iff] at hf ⊢
  intro i
  simp only [coeff_map]
  exact Ideal.le_comap_pow φ i (hf i)

end Lec9Blowups
