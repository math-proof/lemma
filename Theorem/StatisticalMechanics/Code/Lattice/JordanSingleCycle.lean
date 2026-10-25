/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanSingleCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Lattice.JordanZ2.Part3
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartDef.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartNext.Part4
import Theorem.StatisticalMechanics.Code.Lattice.DartInjective
import Theorem.StatisticalMechanics.Code.Lattice.DartOrbit.Part6
import Theorem.StatisticalMechanics.Code.Lattice.TurningNumber.Part6
import Theorem.StatisticalMechanics.Code.Lattice.ContourAnchor.Part5
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Theorem.StatisticalMechanics.Code.Lattice.ContourLinksExits.Part4
import Theorem.StatisticalMechanics.Code.Lattice.OrbitEncloses.Part4
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperUncond.Part6
open Finset Set SimpleGraph Function List


namespace StatMech

namespace Lattice

open StatMech.Percolation (origin)

variable {ω : ConfigSpace (Sym2 (Site 2))}


theorem polygon_edges_nodup {V : Type*} (g : ℕ → V) (p : ℕ) (hp : 3 ≤ p)
    (hper : ∀ k, g k = g (k % p)) (hinj : Set.InjOn g (Set.Iio p)) :
    ((List.range p).map (fun k => s(g k, g (k + 1)))).Nodup := by
  apply List.Nodup.map_on
  · intro i hi j hj h
    rw [List.mem_range] at hi hj
    have hi1 : g (i + 1) = g ((i + 1) % p) := hper (i + 1)
    have hj1 : g (j + 1) = g ((j + 1) % p) := hper (j + 1)
    have hmodi : (i + 1) % p < p := Nat.mod_lt _ (by omega)
    have hmodj : (j + 1) % p < p := Nat.mod_lt _ (by omega)
    have vi : (i + 1) % p = if i + 1 = p then 0 else i + 1 := by
      by_cases hc : i + 1 = p
      · simp [hc]
      · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
    have vj : (j + 1) % p = if j + 1 = p then 0 else j + 1 := by
      by_cases hc : j + 1 = p
      · simp [hc]
      · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
    rw [hi1, hj1, Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact hinj (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hj) h1
    · have e1 : i = (j + 1) % p := hinj (Set.mem_Iio.mpr hi) (Set.mem_Iio.mpr hmodj) h1
      have e2 : (i + 1) % p = j := hinj (Set.mem_Iio.mpr hmodi) (Set.mem_Iio.mpr hj) h2
      rw [vi] at e2; rw [vj] at e1
      split_ifs at e1 e2 <;> omega
  · exact List.nodup_range


theorem polygon_support_tail_nodup {V : Type*} (g : ℕ → V) (p : ℕ) (hp : 1 ≤ p)
    (hper : ∀ k, g k = g (k % p)) (hinj : Set.InjOn g (Set.Iio p)) :
    (((List.range (p + 1)).map g).tail).Nodup := by
  rw [← List.map_tail]
  have htail : (List.range (p + 1)).tail = List.range' 1 p := by
    rw [List.range_succ_eq_map, List.tail_cons, List.range'_eq_map_range]
    congr 1; funext a; omega
  rw [htail]
  apply List.Nodup.map_on
  · intro a ha b hb h
    rw [List.mem_range'] at ha hb
    have hpa : a % p < p := Nat.mod_lt _ (by omega)
    have hpb : b % p < p := Nat.mod_lt _ (by omega)
    rw [hper a, hper b] at h
    have key : a % p = b % p := hinj (Set.mem_Iio.mpr hpa) (Set.mem_Iio.mpr hpb) h
    have va : a % p = if a = p then 0 else a := by
      by_cases hc : a = p
      · simp [hc]
      · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
    have vb : b % p = if b = p then 0 else b := by
      by_cases hc : b = p
      · simp [hc]
      · rw [if_neg hc, Nat.mod_eq_of_lt (by omega)]
    rw [va, vb] at key
    split_ifs at key <;> omega
  · exact List.nodup_range'


theorem orbitFaceWalk_edges (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) (n : ℕ) :
    (dartOrbitFaceWalk K e he n).edges
      = (List.range n).map
        (fun k => s(dartFace ((dartNext K)^[k] e), dartFace ((dartNext K)^[k + 1] e))) := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [dartOrbitFaceWalk, SimpleGraph.Walk.edges_copy, SimpleGraph.Walk.edges_concat, ih,
      List.range_succ, List.map_append]
    simp only [List.concat_eq_append, List.map_cons, List.map_nil]
    rw [Function.iterate_succ_apply']


theorem orbitFaceWalk_isCycle (K : Set (Site 2)) (e : Dart) (he : IsBoundaryDart K e) (p : ℕ)
    (hp : 3 ≤ p) (hcl : (dartNext K)^[p] e = e)
    (hinj : Set.InjOn (fun k => dartFace ((dartNext K)^[k] e)) (Set.Iio p)) :
    ((dartOrbitFaceWalk K e he p).copy rfl (by rw [hcl])).IsCycle := by
  set g : ℕ → Site 2 := fun k => dartFace ((dartNext K)^[k] e) with hg
  have hper : ∀ k, g k = g (k % p) := by
    intro k
    show dartFace ((dartNext K)^[k] e) = dartFace ((dartNext K)^[k % p] e)
    rw [iterate_eq_mod_of_period (dartNext K) e hcl k]
  rw [Walk.isCycle_def]
  refine ⟨?_, ?_, ?_⟩
  · 
    rw [Walk.isTrail_def, Walk.edges_copy, orbitFaceWalk_edges]
    have hrw : (fun k => s(dartFace ((dartNext K)^[k] e), dartFace ((dartNext K)^[k + 1] e)))
        = (fun k => s(g k, g (k + 1))) := rfl
    rw [hrw]
    exact polygon_edges_nodup g p hp hper hinj
  · 
    intro hnil
    have hlen : ((dartOrbitFaceWalk K e he p).copy rfl (by rw [hcl])).length = 0 := by
      rw [hnil]; rfl
    rw [Walk.length_copy, dartOrbitFaceWalk_length] at hlen
    omega
  · 
    rw [Walk.support_copy, dartOrbitFaceWalk_support]
    have hrw : (fun k => dartFace ((dartNext K)^[k] e)) = g := rfl
    rw [hrw]
    exact polygon_support_tail_nodup g p (by omega) hper hinj


end Lattice
end StatMech
