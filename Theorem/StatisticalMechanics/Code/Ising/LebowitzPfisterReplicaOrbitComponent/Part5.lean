/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part4
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.RandomCurrent

open StatMech.GrahamGHS.FourColor

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in

theorem card_lpReplicaCopyIndicesAtEdge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    (lpReplicaCopyIndicesAtEdge G sites m P e).card =
      profileFlux (lpReplicaCurrentGraph G sites) m P e := by
  classical
  let incl : Fin (m e) ↪ Copy (lpReplicaCurrentGraph G sites) m :=
    ⟨fun i => Sigma.mk e i, fun _ _ h => by simpa using h⟩
  have hmap : (lpReplicaCopyIndicesAtEdge G sites m P e).map incl =
      P.filter fun c => c.1 = e := by
    ext c
    constructor
    · intro hc
      obtain ⟨i, hi, hic⟩ := Finset.mem_map.mp hc
      simp only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
        Finset.mem_univ, true_and] at hi
      subst c
      exact Finset.mem_filter.mpr ⟨hi, rfl⟩
    · intro hc
      rw [Finset.mem_filter] at hc
      rcases c with ⟨f, i⟩
      simp only at hc
      obtain rfl := hc.2
      apply Finset.mem_map.mpr
      exact ⟨i, by
        simp only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact hc.1, rfl⟩
  unfold profileFlux
  rw [← hmap, Finset.card_map]


end
end StatMech.Ising
