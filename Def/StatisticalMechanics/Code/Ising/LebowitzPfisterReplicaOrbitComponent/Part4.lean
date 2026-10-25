/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part4
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

def lpReplicaCopySubsetSigmaEquiv
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P} ≃
      Σ e : (lpReplicaCurrentGraph G sites).edgeFinset,
        {c : Copy (lpReplicaCurrentGraph G sites) m //
          c ∈ P.filter (fun d => d.1 = e)} where
  toFun c := ⟨c.1.1, ⟨c.1, by simp [c.2]⟩⟩
  invFun c := ⟨c.2.1, (Finset.mem_filter.mp c.2.2).1⟩
  left_inv := by
    intro c
    rfl
  right_inv := by
    rintro ⟨e, ⟨c, hc⟩⟩
    have he : c.1 = e := (Finset.mem_filter.mp hc).2
    subst e
    rfl


noncomputable def lpReplicaCopyIndicesAtEdge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) : Finset (Fin (m e)) := by
  classical
  exact Finset.univ.filter fun i =>
    (Sigma.mk e i : Copy (lpReplicaCurrentGraph G sites) m) ∈ P

end
end StatMech.Ising
