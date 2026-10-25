/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianFourColorDiagonal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorFamilies.Part2
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianFourColorDiagonal
open Finset
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype V] [DecidableEq V]


@[simp] theorem grahamGlobalMiddleSwap_color1 (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).color1 = q.color1 := rfl

@[simp] theorem grahamGlobalMiddleSwap_color2 (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).color2 = q.color3 := rfl

@[simp] theorem grahamGlobalMiddleSwap_color3 (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).color3 = q.color2 := rfl

@[simp] theorem grahamGlobalMiddleSwap_color4
    (U : Finset ι) (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).color4 U = q.color4 U := by
  unfold GrahamFourColoring.color4 grahamGlobalMiddleSwap
  ext e
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

@[simp] theorem grahamGlobalMiddleSwap_involutive
    (q : GrahamFourColoring ι) :
    grahamGlobalMiddleSwap (grahamGlobalMiddleSwap q) = q := by
  cases q
  rfl

theorem grahamGlobalMiddleSwap_isPartition_iff
    (U : Finset ι) (q : GrahamFourColoring ι) :
    (grahamGlobalMiddleSwap q).IsPartition U ↔ q.IsPartition U := by
  unfold GrahamFourColoring.IsPartition grahamGlobalMiddleSwap
  constructor
  · rintro ⟨h1, h3, h2, h13, h12, h32⟩
    exact ⟨h1, h2, h3, h12, h13, h32.symm⟩
  · rintro ⟨h1, h2, h3, h12, h13, h23⟩
    exact ⟨h1, h3, h2, h13, h12, h23.symm⟩


end StatMech.FrontierA
