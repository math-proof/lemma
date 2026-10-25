/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaRowTagged.Part5
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Def.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality
open Finset
open scoped symmDiff


namespace StatMech.Ising

open StatMech.Sharpness

open StatMech.Sharpness.FluxEdgeCopy

noncomputable section

variable {V I : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]

@[simp] theorem mem_lpReplicaDisconnProfileFamily
    (G : SimpleGraph V) (sites : I -> V)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (S : Finset (Copy (lpReplicaCurrentGraph G sites) m)) :
    S ∈ lpReplicaDisconnProfileFamily G sites A m ↔
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) S = A ∧
      RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m)
        (Finset.univ \ S) = ∅ ∧
      ¬ RandomCurrent.connK
        (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
  classical
  simp [lpReplicaDisconnProfileFamily]


set_option maxHeartbeats 800000 in
theorem lpReplicaDisconnProfileTerm_eq_card_mul_weight
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    lpReplicaDisconnProfileTerm G sites beta J hf r A m =
      (#(lpReplicaDisconnProfileFamily G sites A m) : Real) *
        weight (lpReplicaCurrentGraph G sites) beta
          (lpReplicaCurrentCoupling J hf r)
          (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
  classical
  let H := lpReplicaCurrentGraph G sites
  let Jr := lpReplicaCurrentCoupling J hf r
  let P : Finset (Copy H m) -> Prop := fun S =>
    RandomCurrent.sources (endsM H m) S = A ∧
      RandomCurrent.sources (endsM H m) (Finset.univ \ S) = ∅ ∧
      ¬ RandomCurrent.connK (endsM H m) Finset.univ
        lpReplicaCurrentGhost0 lpReplicaCurrentGhost1
  change ((∑ S : Finset (Copy H m),
      (if RandomCurrent.sources (endsM H m) S = A then (1 : Real) else 0) *
        (if RandomCurrent.sources (endsM H m) (Finset.univ \ S) = ∅
          then 1 else 0) *
        (if ¬ RandomCurrent.connK (endsM H m) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 then 1 else 0)) *
      weight H beta Jr (ofEdgeFun H m)) =
    (#((Finset.univ : Finset (Finset (Copy H m))).filter P) : Real) *
      weight H beta Jr (ofEdgeFun H m)
  congr 1
  calc
    (∑ S : Finset (Copy H m),
        (if RandomCurrent.sources (endsM H m) S = A then (1 : Real) else 0) *
          (if RandomCurrent.sources (endsM H m) (Finset.univ \ S) = ∅
            then 1 else 0) *
          (if ¬ RandomCurrent.connK (endsM H m) Finset.univ
            lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 then 1 else 0)) =
      ∑ S : Finset (Copy H m), if P S then (1 : Real) else 0 := by
      apply Finset.sum_congr rfl
      intro S _
      dsimp only [P]
      by_cases hA : RandomCurrent.sources (endsM H m) S = A <;>
        by_cases hzero : RandomCurrent.sources (endsM H m)
          (Finset.univ \ S) = ∅ <;>
        by_cases hdisc : ¬ RandomCurrent.connK (endsM H m) Finset.univ
          lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <;>
        simp [hA, hzero, hdisc]
    _ = (#((Finset.univ : Finset (Finset (Copy H m))).filter P) : Real) := by
      exact Finset.sum_boole P Finset.univ


theorem lpReplicaCollisionRowGate_of_mem_disconnFamilies
    (G : SimpleGraph V) (sites : I -> V)
    (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
    (Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a))
    (Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b))
    (A B : Finset (LPReplicaCurrentVertex V))
    (hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites A a)
    (hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites B b) :
    LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites a b) A
      (B.map lpReplicaCurrentReflect.toEmbedding)
      (lpReplicaCollisionRowTag G sites a b Sa Sb) := by
  rw [mem_lpReplicaDisconnProfileFamily] at hSa hSb
  exact lpReplicaCollisionRowGate G sites a b Sa Sb A B
    hSa.1 hSa.2.1 hSa.2.2 hSb.1 hSb.2.1 hSb.2.2


theorem lpReplicaDisconnProfileTerm_nonneg
    (G : SimpleGraph V) (sites : I -> V)
    (beta : Real) (J : Sym2 V -> Real) (hf : V -> Real) (r : Real)
    (hbeta : 0 <= beta) (hJ : ∀ e, 0 <= J e)
    (hhf : ∀ x, 0 <= hf x) (hr : 0 <= r)
    (A : Finset (LPReplicaCurrentVertex V))
    (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
    0 <= lpReplicaDisconnProfileTerm G sites beta J hf r A m := by
  classical
  unfold lpReplicaDisconnProfileTerm
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro S _
    positivity
  · exact StatMech.Ising.acw_weight_nonneg
      (lpReplicaCurrentGraph G sites) beta
      (lpReplicaCurrentCoupling J hf r) hbeta
      (lpReplicaCurrentCoupling_nonneg J hf r hJ hhf hr) _


end
end StatMech.Ising
