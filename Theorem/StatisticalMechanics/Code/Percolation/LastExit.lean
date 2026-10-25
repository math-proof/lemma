/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LastExit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecay.Part2
import Theorem.StatisticalMechanics.Code.Percolation.Theta
open MeasureTheory Set SimpleGraph
open scoped NNReal ENNReal


namespace StatMech

namespace Percolation

open StatMech.Lattice


section AbstractWalk

variable {V : Type*} {G : SimpleGraph V}


theorem lastIndexMem {a b : V} (p : G.Walk a b) (S : Set V) [DecidablePred (· ∈ S)]
    (ha : a ∈ S) (hb : b ∉ S) :
    ∃ m, m < p.length ∧ p.getVert m ∈ S ∧
      ∀ n, m < n → n ≤ p.length → p.getVert n ∉ S := by
  classical
  set T : Finset ℕ := (Finset.range (p.length + 1)).filter (fun n => p.getVert n ∈ S) with hT
  have h0 : 0 ∈ T := by
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by rw [Walk.getVert_zero]; exact ha⟩
  have hTne : T.Nonempty := ⟨0, h0⟩
  set m := T.max' hTne with hm
  have hmT : m ∈ T := T.max'_mem hTne
  rw [hT] at hmT
  simp only [Finset.mem_filter, Finset.mem_range] at hmT
  obtain ⟨hmle, hmS⟩ := hmT
  have hmlt : m < p.length := by
    rcases Nat.lt_or_ge m p.length with h | h
    · exact h
    · exact absurd (p.getVert_of_length_le (by omega) ▸ hmS) hb
  refine ⟨m, hmlt, hmS, ?_⟩
  intro n hmn hnle hnS
  have hnT : n ∈ T := by
    rw [hT]; simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hnS⟩
  have := T.le_max' n hnT
  rw [← hm] at this
  omega


theorem drop_avoids_of_after {a b : V} (p : G.Walk a b) (S : Set V) {m : ℕ}
    (hm : m < p.length)
    (hafter : ∀ n, m < n → n ≤ p.length → p.getVert n ∉ S) :
    ∀ z ∈ (p.drop (m + 1)).support, z ∉ S := by
  intro z hz hzS
  rw [Walk.mem_support_iff_exists_getVert] at hz
  obtain ⟨k, hk, hkle⟩ := hz
  rw [Walk.drop_getVert] at hk
  rw [Walk.drop_length] at hkle
  exact hafter (m + 1 + k) (by omega) (by omega) (hk ▸ hzS)


theorem exists_lastExit {a b : V} (p : G.Walk a b) (S : Set V) [DecidablePred (· ∈ S)]
    (ha : a ∈ S) (hb : b ∉ S) :
    ∃ (x y : V) (_hx : x ∈ S) (hy : y ∉ S) (_hadj : G.Adj x y),
      Nonempty ((G.induce {v | v ∉ S}).Walk ⟨y, hy⟩ ⟨b, hb⟩) := by
  classical
  obtain ⟨m, hmlt, hmS, hafter⟩ := lastIndexMem p S ha hb
  have hyS : p.getVert (m + 1) ∉ S := hafter (m + 1) (by omega) (by omega)
  have hadj : G.Adj (p.getVert m) (p.getVert (m + 1)) := p.adj_getVert_succ hmlt
  have hqsupp : ∀ z ∈ (p.drop (m + 1)).support, z ∈ {v | v ∉ S} :=
    fun z hz => drop_avoids_of_after p S hmlt hafter z hz
  refine ⟨p.getVert m, p.getVert (m + 1), hmS, hyS, hadj,
    ⟨((p.drop (m + 1)).induce {v | v ∉ S} hqsupp).copy (by simp) rfl⟩⟩

end AbstractWalk


variable {d : ℕ}


theorem lattice_lastExit (ω : ConfigSpace (Sym2 (Site d))) (K : Set (Site d)) (o v : Site d)
    (ho : o ∈ K) (hv : v ∉ K) (hconn : Connected d ω o v) :
    ∃ (x y : Site d) (_hx : x ∈ K) (hy : y ∉ K), IsOpenEdge d ω x y ∧
      ConnectedWithin d ω {z | z ∉ K} ⟨y, hy⟩ ⟨v, hv⟩ := by
  classical
  obtain ⟨p⟩ := hconn
  obtain ⟨x, y, hx, hy, hadj, ⟨w⟩⟩ := exists_lastExit p K ho hv
  exact ⟨x, y, hx, hy, hadj, ⟨w⟩⟩


end Percolation
end StatMech
