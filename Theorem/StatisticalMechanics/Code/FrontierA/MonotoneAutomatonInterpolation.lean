/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonInterpolation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonLaw.Part4
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInterpolation
open MeasureTheory


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


@[simp] theorem tripleFieldShift_fst (g : Multiplicative (Site d))
    (q : FieldTriple d) : (tripleFieldShift g q).1 = fieldShift g q.1 :=
  rfl

@[simp] theorem tripleFieldShift_snd_fst (g : Multiplicative (Site d))
    (q : FieldTriple d) : (tripleFieldShift g q).2.1 = fieldShift g q.2.1 :=
  rfl

@[simp] theorem tripleFieldShift_snd_snd (g : Multiplicative (Site d))
    (q : FieldTriple d) : (tripleFieldShift g q).2.2 = fieldShift g q.2.2 :=
  rfl

@[simp] theorem tripleFieldShift_one :
    (tripleFieldShift (1 : Multiplicative (Site d)) :
      FieldTriple d → FieldTriple d) = id := by
  funext q
  rcases q with ⟨low, middle, high⟩
  simp [tripleFieldShift]

theorem tripleFieldShift_mul (g h : Multiplicative (Site d)) :
    (tripleFieldShift (g * h) : FieldTriple d → FieldTriple d) =
      tripleFieldShift g ∘ tripleFieldShift h := by
  funext q
  rcases q with ⟨low, middle, high⟩
  simp [tripleFieldShift, fieldShift_mul]

theorem measurable_tripleFieldShift (g : Multiplicative (Site d)) :
    Measurable (tripleFieldShift g : FieldTriple d → FieldTriple d) := by
  exact (measurable_fieldShift g).comp measurable_fst |>.prodMk
    (((measurable_fieldShift g).comp measurable_snd.fst).prodMk
      ((measurable_fieldShift g).comp measurable_snd.snd))


end StatMech.FrontierA
