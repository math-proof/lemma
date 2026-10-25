/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaOrbitComponent.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part17
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaOrbitComponent.Part5
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

@[simp] theorem lpReplicaCopySubsetEquivProfile_edge
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P}) :
    (lpReplicaCopySubsetEquivProfile G sites m P c).1 = c.1.1 := rfl


@[simp] theorem lpReplicaCopySubsetEquivProfile_apply
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P}) :
    lpReplicaCopySubsetEquivProfile G sites m P c =
      Sigma.mk c.1.1
        (((lpReplicaCopyIndicesAtEdge G sites m P c.1.1).orderIsoOfFin
          (card_lpReplicaCopyIndicesAtEdge G sites m P c.1.1)).symm
            ⟨c.1.2, by
              simpa only [lpReplicaCopyIndicesAtEdge, Finset.mem_filter,
                Finset.mem_univ, true_and] using c.2⟩) := by
  rcases c with ⟨⟨e, k⟩, hc⟩
  rfl


theorem lpReplicaCopySubsetEquivProfile_symm_cast
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P Q : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (hPQ : P = Q)
    (d : Copy (lpReplicaCurrentGraph G sites)
      (profileFlux (lpReplicaCurrentGraph G sites) m P)) :
    ((lpReplicaCopySubsetEquivProfile G sites m Q).symm
        (cast (congrArg (Copy (lpReplicaCurrentGraph G sites))
          (congrArg (profileFlux (lpReplicaCurrentGraph G sites) m) hPQ)) d)).1 =
      ((lpReplicaCopySubsetEquivProfile G sites m P).symm d).1 := by
  subst Q
  rfl

theorem lpReplicaCopySubsetEquivProfile_ends
    (G : SimpleGraph V) (sites : I -> V)
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (P : Finset (Copy (lpReplicaCurrentGraph G sites) m))
    (c : {c : Copy (lpReplicaCurrentGraph G sites) m // c ∈ P}) :
    endsM (lpReplicaCurrentGraph G sites)
        (profileFlux (lpReplicaCurrentGraph G sites) m P)
        (lpReplicaCopySubsetEquivProfile G sites m P c) =
      endsM (lpReplicaCurrentGraph G sites) m c.1 := by
  rfl


end
end StatMech.Ising
