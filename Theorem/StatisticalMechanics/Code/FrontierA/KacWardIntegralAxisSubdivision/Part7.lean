/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/KacWardIntegralAxisSubdivision.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisWord.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardForwardSubdivision
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardChordPhaseGlue.Part2
import Theorem.StatisticalMechanics.Code.Onsager.PeriodicTurnClosure.Part9
import Def.StatisticalMechanics.Code.FrontierA.KacWardIntegralAxisSubdivision.Part7


namespace StatMech.FrontierA

open Set

open scoped BigOperators

open StatMech.Onsager.BaseCase


@[simp] theorem kwVectorTurnPhase_self (z : ℂ) :
    kwVectorTurnPhase z z = 1 := by
  simp [kwVectorTurnPhase, kwAngleTurnPhase]

theorem kwVectorPhasePath_replicate (z : ℂ) (N : ℕ) :
    kwVectorPhasePath (List.replicate N z) = 1 := by
  induction N with
  | zero => rfl
  | succ N ih =>
      cases N with
      | zero => rfl
      | succ N =>
          rw [List.replicate_succ, List.replicate_succ,
            kwVectorPhasePath_cons_cons, kwVectorTurnPhase_self]
          simpa using ih

theorem getLastD_eq_getLast_of_ne_nil
    {A : Type*} (l : List A) (default : A) (h : l ≠ []) :
    l.getLastD default = l.getLast h := by
  cases l with
  | nil => exact (h rfl).elim
  | cons x tail => rfl


theorem kwVectorPhasePath_expandedRectilinearBlocks
    (blocks : List (Fin 4 × ℕ))
    (hpos : ∀ block ∈ blocks, 0 < block.2) :
    kwVectorPhasePath (kwExpandedRectilinearBlocks blocks) =
      kwVectorPhasePath (kwCompressedRectilinearBlocks blocks) := by
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
      cases tail with
      | nil =>
          simp [kwExpandedRectilinearBlocks,
            kwCompressedRectilinearBlocks,
            kwVectorPhasePath_replicate]
      | cons next rest =>
          rcases block with ⟨d, N⟩
          rcases next with ⟨e, K⟩
          have hb : 0 < N := hpos (d, N) (by simp)
          have hn : 0 < K := hpos (e, K) (by simp)
          obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
          obtain ⟨c, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
          have htail : ∀ x ∈ (e, c + 1) :: rest, 0 < x.2 := by
            intro x hx
            exact hpos x (by simp [hx])
          have hi := ih htail
          change kwVectorPhasePath
              ((kwRectilinearVector d ::
                List.replicate b (kwRectilinearVector d)) ++
                kwRectilinearVector e ::
                  (List.replicate c (kwRectilinearVector e) ++
                    kwExpandedRectilinearBlocks rest)) = _
          rw [kwVectorPhasePath_append_cons]
          have hbpath : kwVectorPhasePath
              (kwRectilinearVector d ::
                List.replicate b (kwRectilinearVector d)) = 1 := by
            rw [← List.replicate_succ]
            exact kwVectorPhasePath_replicate _ _
          have hblast :
              (kwRectilinearVector d ::
                List.replicate b (kwRectilinearVector d)).getLastD
                  (kwRectilinearVector d) = kwRectilinearVector d := by
            rw [← List.replicate_succ]
            rw [getLastD_eq_getLast_of_ne_nil _ _
                List.replicate_succ_ne_nil,
              List.getLast_replicate_succ]
          have hi' := hi
          change kwVectorPhasePath
              (kwRectilinearVector e ::
                (List.replicate c (kwRectilinearVector e) ++
                  kwExpandedRectilinearBlocks rest)) =
            kwVectorPhasePath
              (kwRectilinearVector e ::
                kwCompressedRectilinearBlocks rest) at hi'
          rw [hbpath, hblast, hi']
          simp only [one_mul]
          change kwVectorTurnPhase (kwRectilinearVector d)
              (kwRectilinearVector e) *
                kwVectorPhasePath
                  (kwRectilinearVector e ::
                    kwCompressedRectilinearBlocks rest) =
            kwVectorPhasePath
              (kwRectilinearVector d :: kwRectilinearVector e ::
                kwCompressedRectilinearBlocks rest)
          rfl

theorem getLastD_append_of_right_ne_nil
    {A : Type*} (left right : List A) (default : A) (h : right ≠ []) :
    (left ++ right).getLastD default = right.getLastD default := by
  rw [getLastD_eq_getLast_of_ne_nil _ _
      (List.append_ne_nil_of_right_ne_nil left h),
    getLastD_eq_getLast_of_ne_nil _ _ h,
    List.getLast_append_of_right_ne_nil]

theorem kwExpandedRectilinearBlocks_getLastD
    (blocks : List (Fin 4 × ℕ))
    (hpos : ∀ block ∈ blocks, 0 < block.2) (default : ℂ) :
    (kwExpandedRectilinearBlocks blocks).getLastD default =
      (kwCompressedRectilinearBlocks blocks).getLastD default := by
  induction blocks with
  | nil => rfl
  | cons block tail ih =>
      rcases block with ⟨d, N⟩
      have hN : 0 < N := hpos (d, N) (by simp)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      cases tail with
      | nil =>
          simp only [kwExpandedRectilinearBlocks,
            kwCompressedRectilinearBlocks, List.flatMap_cons,
            List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil]
          change (List.replicate (k + 1)
              (kwRectilinearVector d)).getLastD default =
            [kwRectilinearVector d].getLastD default
          rw [getLastD_eq_getLast_of_ne_nil _ _
              List.replicate_succ_ne_nil,
            List.getLast_replicate_succ]
          rfl
      | cons next rest =>
          have htail : ∀ x ∈ next :: rest, 0 < x.2 := by
            intro x hx
            exact hpos x (by simp [hx])
          have hexpNe :
              kwExpandedRectilinearBlocks (next :: rest) ≠ [] := by
            have hn : 0 < next.2 := htail next (by simp)
            intro hempty
            have hlen := congrArg List.length hempty
            simp [kwExpandedRectilinearBlocks] at hlen
            omega
          change (List.replicate (k + 1) (kwRectilinearVector d) ++
                kwExpandedRectilinearBlocks (next :: rest)).getLastD default =
              (kwRectilinearVector d ::
                kwCompressedRectilinearBlocks (next :: rest)).getLastD default
          rw [getLastD_append_of_right_ne_nil _ _ _ hexpNe]
          rw [ih htail]
          have hcompNe :
              kwCompressedRectilinearBlocks (next :: rest) ≠ [] := by
            simp [kwCompressedRectilinearBlocks]
          rw [getLastD_eq_getLast_of_ne_nil _ _ hcompNe,
            getLastD_eq_getLast_of_ne_nil _ _ (by simp),
            List.getLast_cons hcompNe]


theorem kwVectorPhaseCycle_expandedRectilinearBlocks
    (blocks : List (Fin 4 × ℕ))
    (hpos : ∀ block ∈ blocks, 0 < block.2) :
    kwVectorPhaseCycle (kwExpandedRectilinearBlocks blocks) =
      kwVectorPhaseCycle (kwCompressedRectilinearBlocks blocks) := by
  cases blocks with
  | nil => rfl
  | cons block tail =>
      rcases block with ⟨d, N⟩
      have hN : 0 < N := hpos (d, N) (by simp)
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      have hpath := kwVectorPhasePath_expandedRectilinearBlocks
        ((d, k + 1) :: tail) hpos
      have hlast := kwExpandedRectilinearBlocks_getLastD
        ((d, k + 1) :: tail) hpos (kwRectilinearVector d)
      change kwVectorPhaseCycle
          (kwRectilinearVector d ::
            (List.replicate k (kwRectilinearVector d) ++
              kwExpandedRectilinearBlocks tail)) =
        kwVectorPhaseCycle
          (kwRectilinearVector d ::
            kwCompressedRectilinearBlocks tail)
      rw [kwVectorPhaseCycle_cons, kwVectorPhaseCycle_cons]
      change kwVectorPhasePath
          (kwExpandedRectilinearBlocks ((d, k + 1) :: tail)) * _ =
        kwVectorPhasePath
          (kwCompressedRectilinearBlocks ((d, k + 1) :: tail)) * _
      rw [hpath]
      change kwVectorPhasePath
          (kwCompressedRectilinearBlocks ((d, k + 1) :: tail)) *
            kwVectorTurnPhase
              ((kwExpandedRectilinearBlocks
                ((d, k + 1) :: tail)).getLastD (kwRectilinearVector d))
              (kwRectilinearVector d) = _
      rw [hlast]
      change kwVectorPhasePath
          (kwCompressedRectilinearBlocks ((d, k + 1) :: tail)) *
            kwVectorTurnPhase
              ((kwRectilinearVector d ::
                kwCompressedRectilinearBlocks tail).getLastD
                  (kwRectilinearVector d))
              (kwRectilinearVector d) = _
      rfl


theorem kwIntegralAxisPolygon_phaseCycle_eq_neg_one
    {n : ℕ} [NeZero n] (p : Fin n → ℤ × ℤ)
    (haxis : ∀ i, (p (i + 1) - p i).1 = 0 ∨
      (p (i + 1) - p i).2 = 0)
    (hsimple : KWRawNonbacktrackingSimpleData
      (fun i ↦ kwIntComplex (p i))) :
    kwVectorPhaseCycle
      (List.ofFn fun i : Fin n ↦ kwIntComplex (p (i + 1) - p i)) = -1 := by
  choose d N hword hstep using fun i : Fin n ↦
    integralAxisWord_eq_replicate_of_axis (haxis i)
  have hdisp (i : Fin n) : p (i + 1) - p i ≠ 0 := by
    rw [sub_ne_zero]
    intro hp
    apply hsimple.edge_ne_zero i
    unfold kwRawEdge
    simpa [hp]
  have hN (i : Fin n) : 0 < N i := by
    apply Nat.pos_of_ne_zero
    intro hzero
    apply hdisp i
    rw [← hstep i, hzero]
    simp
  let blocks : List (Fin 4 × ℕ) :=
    List.ofFn fun i : Fin n ↦ (d i, N i)
  have hblocksPos : ∀ block ∈ blocks, 0 < block.2 := by
    intro block hblock
    simp only [blocks, List.mem_ofFn] at hblock
    obtain ⟨i, rfl⟩ := hblock
    exact hN i
  have hexpanded : kwExpandedRectilinearBlocks blocks =
      (kwIntegralPolygonWord p).map kwRectilinearVector := by
    unfold kwExpandedRectilinearBlocks kwIntegralPolygonWord
    simp only [blocks, List.flatMap, List.map_ofFn,
      List.map_flatten]
    congr 2
    funext i
    simp only [Function.comp_apply, kwIntegralPolygonEdgeWord]
    rw [hword i, List.map_replicate]
  have hcompressed : kwCompressedRectilinearBlocks blocks =
      List.ofFn (fun i : Fin n ↦ kwRectilinearVector (d i)) := by
    simp [kwCompressedRectilinearBlocks, blocks, Function.comp_def]
  have hedgeScale (i : Fin n) :
      kwIntComplex (p (i + 1) - p i) =
        (N i : ℝ) * kwRectilinearVector (d i) := by
    rw [← hstep i, kwIntComplex_nsmul_stepOf]
  have horiginalCompressed :
      kwVectorPhaseCycle
          (List.ofFn fun i : Fin n ↦ kwIntComplex (p (i + 1) - p i)) =
        kwVectorPhaseCycle
          (List.ofFn fun i : Fin n ↦ kwRectilinearVector (d i)) := by
    rw [kwVectorPhaseCycle_ofFn, kwVectorPhaseCycle_ofFn]
    unfold kwLoopPhaseProduct
    apply Finset.prod_congr rfl
    intro i hi
    change kwVectorTurnPhase
        (kwIntComplex (p (i + 1) - p i))
        (kwIntComplex (p (i + 1 + 1) - p (i + 1))) = _
    rw [hedgeScale i, hedgeScale (i + 1)]
    exact kwVectorTurnPhase_pos_scales
      (N i) (N (i + 1)) (by exact_mod_cast hN i)
      (by exact_mod_cast hN (i + 1))
      (kwRectilinearVector (d i)) (kwRectilinearVector (d (i + 1)))
      (kwRectilinearVector_ne_zero _) (kwRectilinearVector_ne_zero _)
  have hlen : 3 ≤ (kwIntegralPolygonWord p).length :=
    hsimple.three_le.trans
      (kwIntegralPolygonWord_vertexCount_le_length p hsimple)
  letI : NeZero (kwIntegralPolygonWord p).length := ⟨by omega⟩
  have hunit := kwIntegralPolygonDirection_phaseProduct_eq_neg_one
    p haxis hsimple
  have hunitCycle : kwVectorPhaseCycle
      ((kwIntegralPolygonWord p).map kwRectilinearVector) = -1 := by
    have hlist : (kwIntegralPolygonWord p).map kwRectilinearVector =
        List.ofFn (fun k : Fin (kwIntegralPolygonWord p).length ↦
          kwRectilinearVector (kwIntegralPolygonDirection p k)) := by
      change (kwIntegralPolygonWord p).map kwRectilinearVector =
        List.ofFn (kwRectilinearVector ∘ kwIntegralPolygonDirection p)
      calc
        (kwIntegralPolygonWord p).map kwRectilinearVector =
            (List.ofFn (kwIntegralPolygonDirection p)).map
              kwRectilinearVector := by
          congr 1
          exact (List.ofFn_get (kwIntegralPolygonWord p)).symm
        _ = List.ofFn
            (kwRectilinearVector ∘ kwIntegralPolygonDirection p) :=
          List.map_ofFn
    rw [hlist, kwVectorPhaseCycle_ofFn]
    simpa only [kwLoopPhaseProduct] using hunit
  calc
    kwVectorPhaseCycle
        (List.ofFn fun i : Fin n ↦ kwIntComplex (p (i + 1) - p i)) =
        kwVectorPhaseCycle
          (List.ofFn fun i : Fin n ↦ kwRectilinearVector (d i)) :=
      horiginalCompressed
    _ = kwVectorPhaseCycle (kwCompressedRectilinearBlocks blocks) := by
      rw [hcompressed]
    _ = kwVectorPhaseCycle (kwExpandedRectilinearBlocks blocks) :=
      (kwVectorPhaseCycle_expandedRectilinearBlocks blocks hblocksPos).symm
    _ = kwVectorPhaseCycle
        ((kwIntegralPolygonWord p).map kwRectilinearVector) := by rw [hexpanded]
    _ = -1 := hunitCycle

end StatMech.FrontierA
