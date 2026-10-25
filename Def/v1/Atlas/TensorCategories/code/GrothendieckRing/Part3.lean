/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/GrothendieckRing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.TensorCategories.code.FrobeniusPerron.Part6
import Lemma.Category.Atlas.v1.TensorCategories.code.FrobeniusPerron
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Defs
import Structure.v1.Atlas.TensorCategories.code.GrothendieckRing.Part2
set_option maxHeartbeats 800000

open Finset


namespace FusionRing

variable {ι : Type*} [DecidableEq ι] [Fintype ι] (R : FusionRing ι)

/-- The integer-valued action of a `FusionRingHom` on `GrRing` elements: linear extension
of the matrix `φ.M` along the basis. -/
def FusionRingHom.grMap
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) (f : GrRing ι) : GrRing κ :=
  fun l => Finset.univ.sum fun i => f i * φ.M i l

/-- The ring homomorphism `GrRingOf R →+* GrRingOf S` induced by a `FusionRingHom`. -/
def FusionRingHom.inducedRingHom
    {ι : Type*} [DecidableEq ι] [Fintype ι]
    {κ : Type*} [DecidableEq κ] [Fintype κ]
    {R : FusionRing ι} {S : FusionRing κ}
    (φ : FusionRingHom R S) :
    GrRingOf R →+* GrRingOf S where
  toFun a := ⟨φ.grMap a.coeff⟩
  map_one' := by
    ext l; show φ.grMap R.grOne l = S.grOne l
    rw [φ.grMap_one]
  map_mul' a b := by
    ext l
    show φ.grMap (R.grMul a.coeff b.coeff) l = S.grMul (φ.grMap a.coeff) (φ.grMap b.coeff) l
    rw [φ.grMap_mul]
  map_zero' := by
    ext l; show (Finset.univ.sum fun i => (0 : GrRingOf R).coeff i * φ.M i l) = 0
    simp
  map_add' a b := by
    ext l
    show φ.grMap (fun k => a.coeff k + b.coeff k) l =
         φ.grMap a.coeff l + φ.grMap b.coeff l
    rw [φ.grMap_add]

end FusionRing

/-- The fusion ring of representations of `ℤ/2`, with basis `Fin 2` and product
given by addition modulo 2. -/
def repZ2 : FusionRing (Fin 2) where
  unit := 0
  N i j k := if (i.val + j.val) % 2 = k.val then 1 else 0
  star := id
  star_star := by decide
  unit_mul := by decide
  mul_unit := by decide
  duality := by decide
  assoc := by decide
  N_star_transpose := by decide

