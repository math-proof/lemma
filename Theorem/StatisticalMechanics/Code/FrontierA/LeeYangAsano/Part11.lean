/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangAsano.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Theorem.StatisticalMechanics.Code.FrontierB.LeeYangPolynomial
import Theorem.StatisticalMechanics.Code.FrontierA.LeeYangSingleEdge.Part3
import Theorem.StatisticalMechanics.Code.FrontierC.LeeYangSymmetry.Part2
import Def.StatisticalMechanics.Code.FrontierA.LeeYangAsano.Part10
open scoped ComplexConjugate


namespace StatMech.FrontierA

open scoped BigOperators

open StatMech.Ising StatMech.FrontierB StatMech.FrontierC

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

theorem leeYangContractList_monomial
    (L : List (V × ↑G.edgeFinset)) (hL : L.Nodup)
    (S : Finset (LeeYangVar G)) (z : LeeYangVar G → ℂ) :
    leeYangContractList G L (leeYangMonomial S) z =
      if LeeYangConsistent G L S then
        leeYangMonomial (leeYangEraseHalves G L S) z else 0 := by
  classical
  induction L generalizing S with
  | nil => simp [leeYangContractList, LeeYangConsistent, leeYangEraseHalves]
  | cons x L ih =>
      have hxL : x ∉ L := (List.nodup_cons.mp hL).1
      have hLT : L.Nodup := (List.nodup_cons.mp hL).2
      let i := leeYangAnchor G x.1
      let j := leeYangHalf G x.1 x.2
      have hij : i ≠ j := by simp [i, j, leeYangAnchor, leeYangHalf]
      have htail : LeeYangConsistent G L (S.erase j) ↔
          LeeYangConsistent G L S := by
        unfold LeeYangConsistent
        apply forall_congr'
        intro y
        apply forall_congr'
        intro hy
        have hyx : y ≠ x := by
          intro h
          subst y
          exact hxL hy
        have hanchor : leeYangAnchor G y.1 ≠ j := by
          simp [j, leeYangAnchor, leeYangHalf]
        have hhalf : leeYangHalf G y.1 y.2 ≠ j := by
          simp [j, leeYangHalf, hyx]
        simp [Finset.mem_erase, hanchor, hhalf]
      have hcons : LeeYangConsistent G (x :: L) S ↔
          (i ∈ S ↔ j ∈ S) ∧ LeeYangConsistent G L S := by
        simp only [LeeYangConsistent, List.mem_cons, forall_eq_or_imp]
        rfl
      simp only [leeYangContractList, List.foldl_cons]
      by_cases hx : i ∈ S ↔ j ∈ S
      · have hfirst : asanoContract (leeYangMonomial S) i j =
            leeYangMonomial (S.erase j) := by
          funext w
          simpa [hx] using asanoContract_monomial S w hij
        change leeYangContractList G L
          (asanoContract (leeYangMonomial S) i j) z = _
        rw [hfirst]
        rw [ih hLT (S.erase j)]
        rw [htail]
        simp only [hcons, hx, true_and]
        rfl
      · have hfirst : asanoContract (leeYangMonomial S) i j = fun _ ↦ 0 := by
          funext w
          simpa [hx] using asanoContract_monomial S w hij
        change leeYangContractList G L
          (asanoContract (leeYangMonomial S) i j) z = _
        rw [hfirst]
        rw [leeYangContractList_zero]
        simp [hcons, hx]

theorem leeYangContractList_sum {A : Type*} [Fintype A] [DecidableEq A]
    (L : List (V × ↑G.edgeFinset)) (p : A → (LeeYangVar G → ℂ) → ℂ) :
    leeYangContractList G L (fun z ↦ ∑ a : A, p a z) =
      fun z ↦ ∑ a : A, leeYangContractList G L (p a) z := by
  induction L generalizing p with
  | nil => rfl
  | cons x L ih =>
      simp only [leeYangContractList, List.foldl_cons]
      rw [show asanoContract (fun z ↦ ∑ a : A, p a z)
          (leeYangAnchor G x.1) (leeYangHalf G x.1 x.2) =
          (fun z ↦ ∑ a : A, asanoContract (p a)
            (leeYangAnchor G x.1) (leeYangHalf G x.1 x.2) z) by
        simpa using asanoContract_sum
          (Finset.univ : Finset A) p (leeYangAnchor G x.1) (leeYangHalf G x.1 x.2)]
      exact ih _

end StatMech.FrontierA
