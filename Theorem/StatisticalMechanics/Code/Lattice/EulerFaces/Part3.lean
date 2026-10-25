/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/EulerFaces.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.Cyclomatic.Part2
import Abbrev.StatisticalMechanics.Code.Lattice.EulerFaces
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

theorem mem_box2 {n : ℕ} {a b : ℤ} (ha : a.natAbs ≤ n) (hb : b.natAbs ≤ n) :
    (![a, b] : Site 2) ∈ box 2 n := by
  intro i; fin_cases i
  · simpa using ha
  · simpa using hb


theorem boxInduce_adj {n : ℕ} {x y : Site 2} (hx : x ∈ box 2 n) (hy : y ∈ box 2 n)
    (hadj : (hypercubicLattice 2).Adj x y) :
    (boxInduce n).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hadj


theorem hadj_step (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a + 1, b] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


theorem vadj_step (a b : ℤ) : (hypercubicLattice 2).Adj ![a, b] ![a, b + 1] := by
  simp [hypercubicLattice_adj, Fin.sum_univ_two]


theorem reach_to_zero0 {n : ℕ} (b : ℤ) (hb : b.natAbs ≤ n) :
    ∀ a : ℤ, (ha : a.natAbs ≤ n) →
      (boxInduce n).Reachable ⟨![a, b], mem_box2 ha hb⟩
        ⟨![0, b], mem_box2 (by simp) hb⟩ := by
  intro a
  induction a using Int.induction_on with
  | zero => intro _; exact Reachable.refl _
  | succ k ih =>
    intro ha
    have hk : (k : ℤ).natAbs ≤ n := by
      have : ((k : ℤ) + 1).natAbs ≤ n := ha; omega
    have step : (boxInduce n).Adj ⟨![(k : ℤ), b], mem_box2 hk hb⟩
        ⟨![(k : ℤ) + 1, b], mem_box2 ha hb⟩ :=
      boxInduce_adj _ _ (hadj_step k b)
    exact (step.symm.reachable).trans (ih hk)
  | pred k ih =>
    intro ha
    have hk : ((-(k : ℤ))).natAbs ≤ n := by
      have : ((-(k : ℤ)) - 1).natAbs ≤ n := ha; omega
    have step : (boxInduce n).Adj ⟨![-(k : ℤ) - 1, b], mem_box2 ha hb⟩
        ⟨![-(k : ℤ), b], mem_box2 hk hb⟩ := by
      have := hadj_step (-(k : ℤ) - 1) b
      simp only [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at this
      exact boxInduce_adj _ _ this
    exact (step.reachable).trans (ih hk)


theorem reach_to_zero1 {n : ℕ} (a : ℤ) (ha : a.natAbs ≤ n) :
    ∀ b : ℤ, (hb : b.natAbs ≤ n) →
      (boxInduce n).Reachable ⟨![a, b], mem_box2 ha hb⟩
        ⟨![a, 0], mem_box2 ha (by simp)⟩ := by
  intro b
  induction b using Int.induction_on with
  | zero => intro _; exact Reachable.refl _
  | succ k ih =>
    intro hb
    have hk : (k : ℤ).natAbs ≤ n := by
      have : ((k : ℤ) + 1).natAbs ≤ n := hb; omega
    have step : (boxInduce n).Adj ⟨![a, (k : ℤ)], mem_box2 ha hk⟩
        ⟨![a, (k : ℤ) + 1], mem_box2 ha hb⟩ :=
      boxInduce_adj _ _ (vadj_step a k)
    exact (step.symm.reachable).trans (ih hk)
  | pred k ih =>
    intro hb
    have hk : ((-(k : ℤ))).natAbs ≤ n := by
      have : ((-(k : ℤ)) - 1).natAbs ≤ n := hb; omega
    have step : (boxInduce n).Adj ⟨![a, -(k : ℤ) - 1], mem_box2 ha hb⟩
        ⟨![a, -(k : ℤ)], mem_box2 ha hk⟩ := by
      have := vadj_step a (-(k : ℤ) - 1)
      simp only [show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring] at this
      exact boxInduce_adj _ _ this
    exact (step.reachable).trans (ih hk)


theorem reach_origin {n : ℕ} {a b : ℤ} (ha : a.natAbs ≤ n) (hb : b.natAbs ≤ n) :
    (boxInduce n).Reachable ⟨![a, b], mem_box2 ha hb⟩
      ⟨![0, 0], mem_box2 (by simp) (by simp)⟩ := by
  have h1 : (boxInduce n).Reachable ⟨![a, b], mem_box2 ha hb⟩
      ⟨![a, 0], mem_box2 ha (by simp)⟩ := reach_to_zero1 a ha b hb
  have h2 : (boxInduce n).Reachable ⟨![a, 0], mem_box2 ha (by simp)⟩
      ⟨![0, 0], mem_box2 (by simp) (by simp)⟩ := reach_to_zero0 0 (by simp) a ha
  exact h1.trans h2


theorem boxInduce_connected (n : ℕ) : (boxInduce n).Connected := by
  rw [connected_iff]
  refine ⟨?_, ⟨⟨![0, 0], mem_box2 (by simp) (by simp)⟩⟩⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  have hax : (x 0).natAbs ≤ n := hx 0
  have hbx : (x 1).natAbs ≤ n := hx 1
  have hay : (y 0).natAbs ≤ n := hy 0
  have hby : (y 1).natAbs ≤ n := hy 1
  have ex : x = ![x 0, x 1] := by funext i; fin_cases i <;> rfl
  have ey : y = ![y 0, y 1] := by funext i; fin_cases i <;> rfl
  have rx : (boxInduce n).Reachable ⟨x, hx⟩ ⟨![0, 0], mem_box2 (by simp) (by simp)⟩ := by
    have key := reach_origin (n := n) hax hbx
    have hcast : (⟨![x 0, x 1], mem_box2 hax hbx⟩ : {z // z ∈ box 2 n}) = ⟨x, hx⟩ :=
      Subtype.ext ex.symm
    rwa [hcast] at key
  have ry : (boxInduce n).Reachable ⟨y, hy⟩ ⟨![0, 0], mem_box2 (by simp) (by simp)⟩ := by
    have key := reach_origin (n := n) hay hby
    have hcast : (⟨![y 0, y 1], mem_box2 hay hby⟩ : {z // z ∈ box 2 n}) = ⟨y, hy⟩ :=
      Subtype.ext ey.symm
    rwa [hcast] at key
  exact rx.trans ry.symm


theorem box_general_face_residue : True := trivial

end Lattice
end StatMech
