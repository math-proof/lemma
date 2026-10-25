/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/Umlaufsatz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.JordanSingleCycle.Part4
open SimpleGraph Function Set


namespace StatMech

namespace Lattice

theorem dartFace_tail_of_dir_right (e : Dart) (hd : e.dir = ![1, 0]) :
    e.tail = ![dartFace e 0, dartFace e 1] := by
  rw [dartFace_of_dir_right e hd]; funext i; fin_cases i <;> simp


theorem dartFace_tail_of_dir_left (e : Dart) (hd : e.dir = ![-1, 0]) :
    e.tail = ![dartFace e 0 + 1, dartFace e 1 + 1] := by
  rw [dartFace_of_dir_left e hd]; funext i; fin_cases i <;> simp


theorem dartFace_tail_of_dir_up (e : Dart) (hd : e.dir = ![0, 1]) :
    e.tail = ![dartFace e 0 + 1, dartFace e 1] := by
  rw [dartFace_of_dir_up e hd]; funext i; fin_cases i <;> simp


theorem dartFace_tail_of_dir_down (e : Dart) (hd : e.dir = ![0, -1]) :
    e.tail = ![dartFace e 0, dartFace e 1 + 1] := by
  rw [dartFace_of_dir_down e hd]; funext i; fin_cases i <;> simp


theorem dartFace_eq_of_dir_eq {e₁ e₂ : Dart} (hdir : e₁.dir = e₂.dir)
    (hface : dartFace e₁ = dartFace e₂) : e₁ = e₂ := by
  apply dart_eq_of_tail_dir _ hdir
  rcases dartDir_cases e₁ with hd | hd | hd | hd <;>
    [ (rw [dartFace_of_dir_right e₁ hd, dartFace_of_dir_right e₂ (hdir ▸ hd)] at hface);
      (rw [dartFace_of_dir_left e₁ hd, dartFace_of_dir_left e₂ (hdir ▸ hd)] at hface);
      (rw [dartFace_of_dir_up e₁ hd, dartFace_of_dir_up e₂ (hdir ▸ hd)] at hface);
      (rw [dartFace_of_dir_down e₁ hd, dartFace_of_dir_down e₂ (hdir ▸ hd)] at hface) ] <;>
  · have h0 := congrFun hface 0
    have h1 := congrFun hface 1
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
    funext i
    fin_cases i
    · show e₁.tail 0 = e₂.tail 0; omega
    · show e₁.tail 1 = e₂.tail 1; omega


theorem orbitDart_injOn (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}) :
    Set.InjOn (fun k => (dartNext K)^[k] a.1) (Set.Iio (dartOrbitPeriod K a)) := by
  intro i hi j hj h
  simp only [mem_Iio] at hi hj
  simp only at h
  have hsub : (dartNextSub K)^[i] a = (dartNextSub K)^[j] a := by
    apply Subtype.ext
    rw [dartNextSub_iterate_val, dartNextSub_iterate_val]
    exact h
  have hmp : dartOrbitPeriod K a = Function.minimalPeriod (dartNextSub K) a := rfl
  exact Function.iterate_injOn_Iio_minimalPeriod (f := dartNextSub K) (x := a)
    (Set.mem_Iio.mpr (by rw [← hmp]; exact hi)) (Set.mem_Iio.mpr (by rw [← hmp]; exact hj)) hsub


end Lattice
end StatMech
