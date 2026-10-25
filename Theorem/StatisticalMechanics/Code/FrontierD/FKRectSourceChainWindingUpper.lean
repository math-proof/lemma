/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectSourceChainWindingUpper.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectSourceSeamWindingUpper.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectSourceChainWindingUpper
open SimpleGraph


namespace StatMech.FrontierD

noncomputable section

theorem connectionPathPairs_pair_mem {V : Type*} [DecidableEq V]
    (n : Nat) (v : Fin (n + 1) -> V) (i : Fin n) :
    (v i.castSucc, v i.succ) ∈ connectionPathPairs n v := by
  exact Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩

theorem connectionPathPairs_card_le {V : Type*} [DecidableEq V]
    (n : Nat) (v : Fin (n + 1) -> V) :
    (connectionPathPairs n v).card <= n := by
  simpa [connectionPathPairs] using
    Finset.card_image_le (s := (Finset.univ : Finset (Fin n)))

theorem connectionPathPairs_card_eq_of_injective
    {V : Type*} [DecidableEq V] (n : Nat) (v : Fin (n + 1) -> V)
    (hinj : Function.Injective
      (fun i : Fin n => (v i.castSucc, v i.succ))) :
    (connectionPathPairs n v).card = n := by
  rw [connectionPathPairs, Finset.card_image_of_injective _ hinj]
  simp


theorem reachable_of_twoPointFun_pos
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    {p q : Real} {x y : V} (hpos : 0 < FK.twoPointFun G p q x y) :
    G.Reachable x y := by
  by_contra hnot
  have hzero : FK.twoPointFun G p q x y = 0 := by
    unfold FK.twoPointFun
    apply Finset.sum_eq_zero
    intro omega homega
    have hnotmem : omega ∉ FK.connEvent G x y := by
      intro hmem
      exact hnot (hmem.mono (FK.openSub_le G omega))
    rw [Set.indicator_of_notMem hnotmem, mul_zero]
  linarith


theorem reachable_first_last_of_connectionPathPairs
    {V : Type*} {G : SimpleGraph V} : forall (n : Nat)
    (v : Fin (n + 1) -> V),
    (forall i : Fin n, G.Reachable (v i.castSucc) (v i.succ)) ->
    G.Reachable (v 0) (v (Fin.last n)) := by
  intro n
  induction n with
  | zero =>
      intro v h
      exact SimpleGraph.Reachable.refl _
  | succ n ih =>
      intro v h
      let v' : Fin (n + 1) -> V := fun i => v i.castSucc
      have hprefix : G.Reachable (v' 0) (v' (Fin.last n)) := by
        apply ih v'
        intro i
        simpa [v'] using h i.castSucc
      have hlast := h (Fin.last n)
      have hzero : v' 0 = v 0 := by rfl
      have hjoin : v' (Fin.last n) = v (Fin.last n).castSucc := by rfl
      have hend : (Fin.last n).succ = Fin.last (n + 1) := by
        apply Fin.ext
        simp
      rw [hjoin] at hprefix
      rw [hend] at hlast
      exact hprefix.trans hlast


end
end StatMech.FrontierD
