/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Theorem.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part2


noncomputable section

open CategoryTheory Category Limits ChainComplex HomologicalComplex

universe v u

namespace FundamentalThm

variable {C : Type u} [Category.{v} C] [Abelian C]

namespace Resolution

variable {Z : C}

/-- Inductive step in constructing the lift: given commuting squares in degrees `n` and `n+1`,
produce a degree-`n+2` lift that fits into the next commuting square. This uses exactness of `Q`
together with projectivity in degree `n+2`. -/
def liftFSucc {Y Z : C} (P : ProjectiveResolution Y) (Q : Resolution Z) (n : ℕ)
    (g : P.complex.X n ⟶ Q.complex.X n)
    (g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 1))
    (w : g' ≫ Q.complex.d (n + 1) n = P.complex.d (n + 1) n ≫ g) :
    Σ' g'' : P.complex.X (n + 2) ⟶ Q.complex.X (n + 2),
      g'' ≫ Q.complex.d (n + 2) (n + 1) = P.complex.d (n + 2) (n + 1) ≫ g' :=
  ⟨(Q.exact_succ n).liftFromProjective (P.complex.d (n + 2) (n + 1) ≫ g') (by simp [w]),
    (Q.exact_succ n).liftFromProjective_comp _ _⟩

/-- Existence half of Theorem 22.1 (Fundamental Theorem of Homological Algebra):
given `f : Y ⟶ Z`, a projective resolution of `Y`, and a resolution of `Z`, we obtain a chain
map `P.complex ⟶ Q.complex` lifting `f`, by assembling the degree-zero, degree-one, and
inductive degree-`n+2` components. -/
def lift {Y Z : C} (f : Y ⟶ Z)
    (P : ProjectiveResolution Y) (Q : Resolution Z) :
    P.complex ⟶ Q.complex :=
  ChainComplex.mkHom _ _ (liftFZero f _ _) (liftFOne f _ _) (liftFOne_zero_comm f P Q)
    fun n ⟨g, g', w⟩ => ⟨(liftFSucc P Q n g g' w).1, (liftFSucc P Q n g g' w).2⟩

end Resolution
end FundamentalThm
end
