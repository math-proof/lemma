/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/DecorationLoopWalk.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Onsager.DecorationTransitionWalk.Part4
import Theorem.StatisticalMechanics.Code.Onsager.DecorationCycleWeight
import Def.StatisticalMechanics.Code.Onsager.DecorationLoopWalk.Part4


namespace StatMech.Onsager

open Finset SimpleGraph

theorem ons_decWalkOfKWChain_edgeCount
    (L : ℕ) [Fact (2 < L)] (start : ons_Dart L)
    (tail : List (ons_Dart L))
    (hchain : List.IsChain (ons_decGeometricStep L) (start :: tail)) :
    ons_decWalkEdgeCount (ons_decWalkOfKWChain L start tail hchain) =
      ons_decKWChainExponent L start tail := by
  induction tail generalizing start with
  | nil =>
      change Multiset.toFinsupp (0 : Multiset (ons_DecEdge L)) = 0
      simp
  | cons target rest ih =>
      have hstep : target.1 = ons_dirStep L start.2 start.1 :=
        hchain.rel
      have htail : List.IsChain (ons_decGeometricStep L) (target :: rest) :=
        hchain.tail
      simp only [ons_decWalkOfKWChain]
      unfold ons_decWalkEdgeCount
      rw [SimpleGraph.Walk.edges_append]
      change Multiset.toFinsupp
          ((ons_decTransitionWalk L target start hstep).edges +
            (ons_decWalkOfKWChain L target rest htail).edges :
              Multiset (ons_DecEdge L)) = _
      rw [Multiset.toFinsupp_add]
      have htrans :=
        ons_decTransitionExponent_eq_edgeCount L target start hstep
      unfold ons_decWalkEdgeCount at htrans
      rw [← htrans]
      have hrest := ih target htail
      unfold ons_decWalkEdgeCount at hrest
      rw [hrest]
      rfl

theorem ons_decWalkOfKWChain_externalDarts
    (L : ℕ) [Fact (2 < L)] (start : ons_Dart L)
    (tail : List (ons_Dart L))
    (hchain : List.IsChain (ons_decGeometricStep L) (start :: tail)) :
    ons_decWalkExternalDarts
        (ons_decWalkOfKWChain L start tail hchain) =
      (start :: tail).dropLast := by
  induction tail generalizing start with
  | nil => rfl
  | cons target rest ih =>
      have hstep : target.1 = ons_dirStep L start.2 start.1 :=
        hchain.rel
      have htail : List.IsChain (ons_decGeometricStep L) (target :: rest) :=
        hchain.tail
      change ons_decWalkExternalDarts
          ((ons_decTransitionWalk L target start hstep).append
            (ons_decWalkOfKWChain L target rest htail)) = _
      rw [ons_decWalkExternalDarts_append,
        ons_decTransitionWalk_externalDarts L target start hstep]
      rw [ih target htail]
      simp

theorem ons_decWalkOfKWChain_snd
    (L : ℕ) (start target : ons_Dart L)
    (rest : List (ons_Dart L))
    (hchain : List.IsChain (ons_decGeometricStep L)
      (start :: target :: rest)) :
    (ons_decWalkOfKWChain L start (target :: rest) hchain).snd =
      ons_dartRev L start := by
  have hstep : target.1 = ons_dirStep L start.2 start.1 := hchain.rel
  have htail : List.IsChain (ons_decGeometricStep L) (target :: rest) :=
    hchain.tail
  have hstart : (target.1, start.2 + 2) = ons_dartRev L start := by
    apply Prod.ext
    · exact hstep.trans (ons_dartRev_fst_eq_step L start).symm
    · simp [ons_dartRev]
  change ((ons_decTransitionWalk L target start hstep).append
    (ons_decWalkOfKWChain L target rest htail)).snd = _
  simp [ons_decTransitionWalk, hstart]

theorem ons_decWalkOfKWChain_snd_of_ne_nil
    (L : ℕ) (start : ons_Dart L) (tail : List (ons_Dart L))
    (hchain : List.IsChain (ons_decGeometricStep L) (start :: tail))
    (htail : tail ≠ []) :
    (ons_decWalkOfKWChain L start tail hchain).snd =
      ons_dartRev L start := by
  cases tail with
  | nil => exact (htail rfl).elim
  | cons target rest =>
      exact ons_decWalkOfKWChain_snd L start target rest hchain

theorem ons_decKWChainExponent_closed_eq_sum
    (L : ℕ) {n : ℕ} [NeZero n] (f : Fin n → ons_Dart L) :
    let states := List.ofFn f
    ons_decKWChainExponent L (f 0) (states.tail ++ [f 0]) =
      ∑ k : Fin n, ons_decTransitionExponent L (f (k + 1)) (f k) := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  let states := List.ofFn f
  have htail : states.tail = List.ofFn (fun i : Fin m ↦ f i.succ) := by
    simp [states, List.ofFn_succ]
  change ons_decKWChainExponent L (f 0)
      (states.tail ++ [f 0]) = _
  rw [ons_decKWChainExponent_eq_zipWith]
  rw [htail]
  rw [← List.sum_ofFn]
  apply congrArg List.sum
  apply List.ext_getElem
  · simp
  · intro i hi h'i
    simp only [List.length_zipWith] at hi
    simp only [List.getElem_zipWith]
    rw [List.getElem_ofFn]
    have hiN : i < m + 1 := by simpa using h'i
    let k : Fin (m + 1) := ⟨i, hiN⟩
    have hsource :
        (f 0 :: (List.ofFn (fun j : Fin m ↦ f j.succ) ++ [f 0]))[i] =
          f k := by
      cases i with
      | zero => simp [k]
      | succ i =>
          have hiM : i < m := by omega
          simp [List.getElem_append, hiM, k]
    have htarget :
        (List.ofFn (fun j : Fin m ↦ f j.succ) ++ [f 0])[i] =
          f (k + 1) := by
      by_cases hiM : i < m
      · simp [List.getElem_append, hiM, k]
        congr 1
        apply Fin.ext
        have hk : k < Fin.last m := by
          change i < m
          exact hiM
        exact (Fin.val_add_one_of_lt hk).symm
      · have hiEq : i = m := by omega
        subst i
        simp only [List.getElem_append, List.length_ofFn, lt_self_iff_false,
          ↓reduceDIte, Nat.sub_self, List.getElem_singleton,
          Fin.isValue]
        congr 1
        apply Fin.ext
        have hklast : k = Fin.last m := by
          apply Fin.ext
          simp [k]
        rw [hklast, Fin.last_add_one]
    rw [hsource, htarget]

end StatMech.Onsager
