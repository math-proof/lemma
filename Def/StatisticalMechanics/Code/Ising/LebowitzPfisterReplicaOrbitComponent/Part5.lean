/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part5
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

noncomputable def lpReplicaCopiesAtEdgeEquivIndices
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (e : (lpReplicaCurrentGraph G sites).edgeFinset) :
    {c : Copy (lpReplicaCurrentGraph G sites) m //
      c ∈ P.filter (fun d => d.1 = e)} ≃
      {i : Fin (m e) // i ∈ lpReplicaCopyIndicesAtEdge G sites m P e} := by
  classical
  let toFun : {c : Copy (lpReplicaCurrentGraph G sites) m //
      c ∈ P.filter (fun d => d.1 = e)} ->
      {i : Fin (m e) //
        i ∈ lpReplicaCopyIndicesAtEdge G sites m P e} := fun c => by
    rcases c with ⟨⟨f, i⟩, hc⟩
    have hfe : f = e := (Finset.mem_filter.mp hc).2
    subst f
    exact ⟨i, by
      simp only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact (Finset.mem_filter.mp hc).1⟩
  let invFun : {i : Fin (m e) //
      i ∈ lpReplicaCopyIndicesAtEdge G sites m P e} ->
      {c : Copy (lpReplicaCurrentGraph G sites) m //
        c ∈ P.filter (fun d => d.1 = e)} := fun i =>
    ⟨Sigma.mk e i.1, Finset.mem_filter.mpr ⟨by
      simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
        Finset.mem_univ, true_and] using i.2, rfl⟩⟩
  exact {
    toFun := toFun
    invFun := invFun
    left_inv := by
      rintro ⟨⟨f, i⟩, hc⟩
      have hfe : f = e := (Finset.mem_filter.mp hc).2
      subst f
      rfl
    right_inv := by
      rintro ⟨i, hi⟩
      rfl
  }


def lpReplicaCopySubsetEquivProfile
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P} ≃
      Copy (lpReplicaCurrentGraph G sites)
        (profileFlux (lpReplicaCurrentGraph G sites) m P) :=
  (lpReplicaCopySubsetSigmaEquiv G sites m P).trans
    (Equiv.sigmaCongrRight fun e =>
      (lpReplicaCopiesAtEdgeEquivIndices G sites m P e).trans
        ((lpReplicaCopyIndicesAtEdge G sites m P e).orderIsoOfFin
          (card_lpReplicaCopyIndicesAtEdge G sites m P e)).symm.toEquiv)

end
end StatMech.Ising
