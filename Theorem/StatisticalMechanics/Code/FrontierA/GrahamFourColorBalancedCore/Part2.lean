/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part3
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem colorClass_subset (m : Finset ι) (c : ↑m → Fin 4) (a : Fin 4) :
    colorClass m c a ⊆ m := by
  intro i hi
  simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hi
  obtain ⟨j, _, rfl⟩ := hi
  exact j.2

theorem colorClass_disjoint (m : Finset ι) (c : ↑m → Fin 4) {a b : Fin 4} (hab : a ≠ b) :
    Disjoint (colorClass m c a) (colorClass m c b) := by
  rw [Finset.disjoint_left]
  intro i hia hib
  simp only [colorClass, Finset.mem_map, Finset.mem_filter, Finset.mem_attach] at hia hib
  obtain ⟨ia, ⟨_, hca⟩, hia⟩ := hia
  obtain ⟨ib, ⟨_, hcb⟩, hib⟩ := hib
  have hieq : ia = ib := Subtype.ext (hia.trans hib.symm)
  subst ib
  exact hab (hca.symm.trans hcb)

theorem connK_mono {ends : ι → Sym2 W} {K L : Finset ι} (hKL : K ⊆ L) {u v : W} :
    Sharpness.RandomCurrent.connK ends K u v → Sharpness.RandomCurrent.connK ends L u v := by
  apply Relation.ReflTransGen.mono
  rintro a b ⟨i, hi, ha, hb, hab⟩
  exact ⟨i, hKL hi, ha, hb, hab⟩


end FourColor
end GrahamGHS
end StatMech
