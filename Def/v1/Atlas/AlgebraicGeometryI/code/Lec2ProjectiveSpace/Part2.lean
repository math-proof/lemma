/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2ProjectiveSpace.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Topology.Order
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.Topology.Constructions
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec2ProjectiveSpace
set_option maxHeartbeats 800000

open scoped LinearAlgebra.Projectivization


noncomputable section

namespace Formalization

variable {k : Type*} [Field k] {n : ℕ}

/-- A function `f : U → k` on an open subset `U ⊆ P^n` is *regular* (Lecture 2, Def 4) if locally
on the affine cone it can be written as a ratio `p/q` of polynomials with `q` non-vanishing. -/
def ProjectiveSpace.IsRegular
    (U : Set (ProjectiveSpace k n)) (f : ↥U → k) : Prop :=
  ∀ (v : PuncturedAffineSpace k n) (_ : ProjectiveSpace.π k n v ∈ U),
    ∃ (p q : MvPolynomial (Fin (n + 1)) k),
      ∃ V : Set (Fin (n + 1) → k),
        @IsOpen _ (zariskiTopologyAffine k n) V ∧
        (v : Fin (n + 1) → k) ∈ V ∧
        ∀ w ∈ V, (hw : w ≠ 0) →
          ∀ (hmem : ProjectiveSpace.π k n ⟨w, hw⟩ ∈ U),
            MvPolynomial.eval w q ≠ 0 ∧
            f ⟨ProjectiveSpace.π k n ⟨w, hw⟩, hmem⟩ =
              MvPolynomial.eval w p / MvPolynomial.eval w q

end Formalization
end
