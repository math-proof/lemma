/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.CategoryTheory.Groupoid
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.GradedObject
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Algebra.Pi
import Abbrev.v1.Atlas.TensorCategories.code.GroupoidMultitensor
set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


namespace GroupoidMultitensor

attribute [instance] FiniteGroupoidData.finObj FiniteGroupoidData.finMor

attribute [instance] FiniteGroupoidData.decEqObj FiniteGroupoidData.decEqMor

/-- If `G` has a single object, `EndUnit k` is `k`-linearly equivalent to `k`. -/
noncomputable def FiniteGroupoidData.endUnitLinearEquivOfSingleObject
    (G : FiniteGroupoidData) (k : Type w) [Field k]
    (h : G.IsSingleObject) : G.EndUnit k ≃ₗ[k] k := by
  have : Nonempty (Unique G.Obj) := Fintype.card_eq_one_iff_nonempty_unique.mp h
  letI := this.some
  exact LinearEquiv.funUnique G.Obj k k

/-- If `G` has a single object, `EndUnit k` is `k`-algebra-equivalent to `k`. -/
noncomputable def FiniteGroupoidData.endUnitAlgEquivOfSingleObject
    (G : FiniteGroupoidData) (k : Type w) [Field k]
    (h : G.IsSingleObject) : G.EndUnit k ≃ₐ[k] k := by
  have : Nonempty (Unique G.Obj) := Fintype.card_eq_one_iff_nonempty_unique.mp h
  letI := this.some
  exact AlgEquiv.funUnique k G.Obj k

/-- View a finite group as the single-object groupoid whose morphisms are the group elements. -/
def groupAsGroupoidData (G : Type u) [Group G] [Fintype G] [DecidableEq G] :
    FiniteGroupoidData.{0, u} where
  Obj := Unit
  Mor := G
  src := fun _ => ()
  tgt := fun _ => ()
  comp := fun g h _ => g * h
  id := fun _ => 1
  inv := fun g => g⁻¹
  src_id := fun _ => rfl
  tgt_id := fun _ => rfl
  src_comp := fun _ _ _ => rfl
  tgt_comp := fun _ _ _ => rfl
  src_inv := fun _ => rfl
  tgt_inv := fun _ => rfl

/-- The pair groupoid on a finite set `X`: objects are points of `X`, with a unique morphism
between any two of them. -/
def pairGroupoidData (X : Type u) [Fintype X] [DecidableEq X] :
    FiniteGroupoidData.{u, u} where
  Obj := X
  Mor := X × X
  src := Prod.fst
  tgt := Prod.snd
  comp := fun g h _ => (g.1, h.2)
  id := fun x => (x, x)
  inv := fun g => (g.2, g.1)
  src_id := fun _ => rfl
  tgt_id := fun _ => rfl
  src_comp := fun _ _ _ => rfl
  tgt_comp := fun _ _ _ => rfl
  src_inv := fun _ => rfl
  tgt_inv := fun _ => rfl

/-- The transformation groupoid `X ⋊ G` associated with a finite group acting on a finite set:
objects are points of `X`, morphisms are pairs `(g, x)` from `x` to `g • x`. -/
def transformationGroupoidData (G : Type u) (X : Type u)
    [Group G] [Fintype G] [DecidableEq G] [Fintype X] [DecidableEq X]
    [MulAction G X] :
    FiniteGroupoidData.{u, u} where
  Obj := X
  Mor := G × X
  src := fun p => p.2
  tgt := fun p => p.1 • p.2
  comp := fun g h _ => (h.1 * g.1, g.2)
  id := fun x => (1, x)
  inv := fun p => (p.1⁻¹, p.1 • p.2)
  src_id := fun _ => rfl
  tgt_id := fun x => by simp
  src_comp := fun _ _ _ => rfl
  tgt_comp := fun g h p => by
    simp only
    rw [mul_smul, p]
  src_inv := fun _ => rfl
  tgt_inv := fun p => by simp

end GroupoidMultitensor
