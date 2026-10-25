/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rbtbutterfly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Order.WellFoundedSet
import Theorem.StatisticalMechanics.Code.Walls.rbtbutterfly.Part3
open Finset
open scoped BigOperators


namespace StatMech.Walls.Reimer

set_option linter.style.longLine false


open Classical in

noncomputable def rbt_Red {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Finset (rbt_Q m) :=
  Finset.univ.filter (fun x => ∃ y ∈ T, rbt_inRed (body y) y x)

open Classical in

noncomputable def rbt_Yellow {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Finset (rbt_Q m) :=
  Finset.univ.filter (fun x => ∃ y ∈ T, rbt_inYellow (body y) y x)


def rbt_G_indep : Prop :=
  ∀ (m : ℕ) (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)),
    LinearIndependent ℝ (fun y : T => rbt_g (body ↑y) ↑y)


open Classical in

noncomputable def rbt_Ybar {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Finset (rbt_Q m) := Finset.univ \ rbt_Yellow body T

open Classical in

noncomputable def rbt_Rbar {m : ℕ} (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)) :
    Finset (rbt_Q m) := rbt_Yellow body T \ rbt_Red body T


def rbt_ButterflyLinIndep : Prop :=
  ∀ (m : ℕ) (body : rbt_Q m → rbt_Q m) (T : Finset (rbt_Q m)),
    LinearIndependent ℝ
      (Sum.elim (fun y : T => rbt_g (body ↑y) ↑y)
        (Sum.elim (fun x : rbt_Ybar body T => rbt_f ↑x)
          (fun x : rbt_Rbar body T => rbt_e ↑x)))

end StatMech.Walls.Reimer
