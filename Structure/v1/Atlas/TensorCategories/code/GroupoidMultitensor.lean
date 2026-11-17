/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GroupoidMultitensor.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Groupoid
public import Mathlib.CategoryTheory.Monoidal.Category
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.GradedObject
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Algebra.Pi
public section

set_option maxHeartbeats 800000

open CategoryTheory

universe u v w


namespace GroupoidMultitensor

/-- A finite groupoid presented combinatorially as objects `Obj`, morphisms `Mor`, source/target
maps, composition (defined when `tgt g = src h`), identity, and inverse, all subject to the
expected groupoid relations. -/
structure FiniteGroupoidData where
  Obj : Type u
  Mor : Type v
  [finObj : Fintype Obj]
  [finMor : Fintype Mor]
  [decEqObj : DecidableEq Obj]
  [decEqMor : DecidableEq Mor]
  src : Mor → Obj
  tgt : Mor → Obj
  comp : (g h : Mor) → tgt g = src h → Mor
  id : Obj → Mor
  inv : Mor → Mor
  src_id : ∀ x, src (id x) = x
  tgt_id : ∀ x, tgt (id x) = x
  src_comp : ∀ g h (p : tgt g = src h), src (comp g h p) = src g
  tgt_comp : ∀ g h (p : tgt g = src h), tgt (comp g h p) = tgt h
  src_inv : ∀ g, src (inv g) = tgt g
  tgt_inv : ∀ g, tgt (inv g) = src g

end GroupoidMultitensor
