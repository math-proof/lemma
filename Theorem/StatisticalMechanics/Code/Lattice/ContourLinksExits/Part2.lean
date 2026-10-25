/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/ContourLinksExits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConnected.Part2
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
import Def.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part2
open Finset Set SimpleGraph Function


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


@[simp] theorem leftExitDart_tail (hfin : (cluster 2 ω (origin 2)).Finite) :
    (leftExitDart (ω := ω) hfin).tail = leftAxisSite (leftExitIndex (ω := ω) hfin) := rfl

@[simp] theorem leftExitDart_head (hfin : (cluster 2 ω (origin 2)).Finite) :
    (leftExitDart (ω := ω) hfin).head = leftAxisSite (leftExitIndex (ω := ω) hfin + 1) := rfl


theorem leftExitDart_isBoundaryDart (hfin : (cluster 2 ω (origin 2)).Finite) :
    IsBoundaryDart (cluster 2 ω (origin 2)) (leftExitDart (ω := ω) hfin) :=
  ⟨leftAxisSite_exit_mem (ω := ω) hfin, leftAxisSite_exit_succ_not_mem (ω := ω) hfin⟩


theorem leftExitDart_dir (hfin : (cluster 2 ω (origin 2)).Finite) :
    (leftExitDart (ω := ω) hfin).dir = ![-1, 0] := by
  rw [Dart.dir_def, leftExitDart_head, leftExitDart_tail, leftAxisSite_succ_eq, leftAxisSite_eq]
  funext i; fin_cases i
  · simp; ring
  · simp


theorem dartDir_cases (e : Dart) :
    e.dir = ![1, 0] ∨ e.dir = ![-1, 0] ∨ e.dir = ![0, 1] ∨ e.dir = ![0, -1] := by
  have h := unitWt_dir e
  unfold unitWt at h
  rw [Fin.sum_univ_two] at h
  set a := e.dir 0 with ha
  set b := e.dir 1 with hb
  have hd : e.dir = ![a, b] := by funext i; fin_cases i <;> rfl
  have hh : a.natAbs + b.natAbs = 1 := h
  have hcase : (a = 1 ∧ b = 0) ∨ (a = -1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) ∨ (a = 0 ∧ b = -1) := by
    omega
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [hd, h1, h2]
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))


end Lattice
end StatMech
