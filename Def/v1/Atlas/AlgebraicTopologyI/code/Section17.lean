/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section16
import Def.v1.Atlas.AlgebraicTopologyI.code.Section16.Part4
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section17


noncomputable section

namespace RealProjectiveSpace

open AlgebraicTopologyI CategoryTheory

/-- The antipodal equivalence on $S^n$: $x \sim y$ iff $y = x$ or $y = -x$. The quotient by
this relation is real projective space $\mathbf{RP}^n$. -/
def antipodalSetoid (n : ℕ) : Setoid (Sphere n) where
  r x y := (x : EuclideanSpace ℝ (Fin (n + 1))) = y ∨
            (x : EuclideanSpace ℝ (Fin (n + 1))) = -↑y
  iseqv := {
    refl := fun _ => Or.inl rfl
    symm := fun {_ y} h => h.elim (fun h => Or.inl h.symm)
      (fun h => Or.inr (by rw [h]; simp [neg_neg]))
    trans := fun {_ y _} hxy hyz => by
      rcases hxy with hxy | hxy <;> rcases hyz with hyz | hyz
      · exact Or.inl (hxy.trans hyz)
      · exact Or.inr (by rw [hxy]; exact hyz)
      · exact Or.inr (by rw [hxy, hyz])
      · exact Or.inl (by rw [hxy, hyz, neg_neg])
  }

/-- Real projective $n$-space $\mathbf{RP}^n = S^n / \{\pm 1\}$, the quotient of $S^n$ by the
antipodal action. -/
def RPn (n : ℕ) : Type :=
  Quotient (antipodalSetoid n)

end RealProjectiveSpace
end
