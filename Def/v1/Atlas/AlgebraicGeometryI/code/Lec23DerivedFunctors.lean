/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec23DerivedFunctors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Structure.v1.Atlas.AlgebraicGeometryI.code.Lec23DerivedFunctors
set_option maxHeartbeats 800000

open CategoryTheory Category Limits


noncomputable section

universe v u

namespace Lec23

attribute [instance] DeltaFunctor.additive

/-- A δ-functor is effaceable if for every `n > 0` and every object `M`, there is a
monomorphism `M ↪ N` killed by `Tⁿ`. Grothendieck's criterion says effaceable δ-functors
are universal. -/
def DeltaFunctor.IsEffaceable {A : Type u} [Category.{v} A] [Abelian A]
    {B : Type*} [Category B] [Abelian B]
    (T : DeltaFunctor A B) : Prop :=
  ∀ (n : ℕ) (_ : 0 < n) (M : A),
    ∃ (N : A) (φ : M ⟶ N), Mono φ ∧ (T.T n).map φ = 0

/-- Proposition 42 (snake lemma): the connecting homomorphism
`Hⁱ(S.X₃) → Hʲ(S.X₁)` for a short exact sequence of complexes. -/
def prop42_connectingHom
    {C : Type*} [Category C] [Abelian C]
    {ι : Type*} {c : ComplexShape ι}
    {S : ShortComplex (HomologicalComplex C c)}
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  hS.δ i j hij

end Lec23
end
