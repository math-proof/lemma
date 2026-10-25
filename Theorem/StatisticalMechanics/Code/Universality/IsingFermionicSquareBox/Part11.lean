/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareBox.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Universality.IsingFermionicMedialComplex.Part7
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareFiniteDuality
import Theorem.StatisticalMechanics.Code.Lattice.EarContraction.Part9
import Mathlib.Combinatorics.SimpleGraph.Matching
import Structure.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareOrientedEdge_nonempty (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n)) :
    Nonempty (FKIsingSquareEdgeOrientation n e) := by
  rcases e with ⟨e, he⟩
  induction e using Sym2.ind with
  | _ x y =>
    rw [SimpleGraph.mem_edgeSet] at he
    have hxy : (hypercubicLattice 2).Adj x.1 y.1 := he
    rcases adj_neighbor_cases x.1 y.1 hxy with h | h | h | h
    · refine ⟨⟨y, x, by
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩, .horizontal, ?_⟩⟩
      simpa using h
    · refine ⟨⟨x, y, rfl, .horizontal, ?_⟩⟩
      funext i
      fin_cases i
      · have hi := congrFun h 0
        simp [Matrix.cons_val_zero, Pi.add_apply] at hi ⊢
        omega
      · have hi := congrFun h 1
        simp [Matrix.cons_val_one, Pi.add_apply] at hi ⊢
        omega
    · refine ⟨⟨y, x, by
          rw [Sym2.eq_iff]
          exact Or.inr ⟨rfl, rfl⟩, .vertical, ?_⟩⟩
      simpa using h
    · refine ⟨⟨x, y, rfl, .vertical, ?_⟩⟩
      funext i
      fin_cases i
      · have hi := congrFun h 0
        simp [Matrix.cons_val_zero, Pi.add_apply] at hi ⊢
        omega
      · have hi := congrFun h 1
        simp [Matrix.cons_val_one, Pi.add_apply] at hi ⊢
        omega


theorem fkIsingSquareOrientedEdge_unique (n : Nat)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (a b : FKIsingSquareEdgeOrientation n e) : a = b := by
  rcases a with ⟨ta, ah, ae, aa, astep⟩
  rcases b with ⟨bt, bh, be, ba, bstep⟩
  have hedge : s(ta, ah) = s(bt, bh) := ae.trans be.symm
  rcases Sym2.eq_iff.mp hedge with hsame | hswap
  · rcases hsame with ⟨rfl, rfl⟩
    cases aa <;> cases ba
    · rfl
    · exfalso
      have h0 := congrFun (astep.symm.trans bstep) 0
      simp [Matrix.cons_val_zero, Pi.add_apply] at h0
    · exfalso
      have h0 := congrFun (astep.symm.trans bstep) 0
      simp [Matrix.cons_val_zero, Pi.add_apply] at h0
    · rfl
  · rcases hswap with ⟨h1, h2⟩
    cases aa <;> cases ba
    · exfalso
      have ha0 := congrFun astep 0
      have hb0 := congrFun bstep 0
      rw [h1, h2] at ha0
      simp [Matrix.cons_val_zero, Pi.add_apply] at ha0 hb0
      omega
    · exfalso
      have ha0 := congrFun astep 0
      have hb0 := congrFun bstep 0
      rw [h1, h2] at ha0
      simp [Matrix.cons_val_zero, Pi.add_apply] at ha0 hb0
      omega
    · exfalso
      have ha1 := congrFun astep 1
      have hb1 := congrFun bstep 1
      rw [h1, h2] at ha1
      simp [Matrix.cons_val_one, Pi.add_apply] at ha1 hb1
      omega
    · exfalso
      have ha1 := congrFun astep 1
      have hb1 := congrFun bstep 1
      rw [h1, h2] at ha1
      simp [Matrix.cons_val_one, Pi.add_apply] at ha1 hb1
      omega


end
end StatMech.Universality
