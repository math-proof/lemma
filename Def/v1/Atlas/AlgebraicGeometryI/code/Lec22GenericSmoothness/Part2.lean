/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec22GenericSmoothness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec22GenericSmoothness


noncomputable section

namespace Lec22

open MvPolynomial

/-- The hypersurface `V(f)` cuts `X` transversally: at every point of `X` where `f`
vanishes, some partial derivative of `f` is nonzero. -/
def IsSmooth_Intersection (k : Type*) [CommRing k] (n : ℕ)
    (f : MvPolynomial (Fin (n + 1)) k)
    (X : SmoothProjVariety k n) : Prop :=
  ∀ x ∈ X.points,
    MvPolynomial.eval x f = 0 →
    ∃ i : Fin (n + 1), MvPolynomial.eval x (MvPolynomial.pderiv i f) ≠ 0

/-- The Zariski topology on the parameter space of degree-`d` hypersurfaces in `ℙⁿ`,
used to formulate "generic" properties. -/
def smoothProjSpace (k : Type*) [CommRing k] (n : ℕ) : SmoothProjVariety k n where
  definingPolys := ∅
  points := { x | ∃ i : Fin (n + 1), x i ≠ 0 }
  points_nonzero := fun _ hx => hx
  points_vanish := fun _ _ _ hf => absurd hf (Set.notMem_empty _)
  dim := n
  smooth := fun _ _ _ hg => absurd hg (Set.notMem_empty _)

end Lec22
end
