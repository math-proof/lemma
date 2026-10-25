/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/MeanfieldPercoInhom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.Pivotal.Part2
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerButterfly
import Theorem.StatisticalMechanics.Code.Inequalities.ReimerFiberClose.Part2
import Theorem.StatisticalMechanics.Code.FK.RussoDerivativeBetaSum
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInhom.Part2
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldPercoInhom
open Finset SimpleGraph Set


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem mpi_mem_blockedSet_iff (B : Set V) (omega : ConfigSpace (Sym2 V)) (x : V) :
    x ∈ mpiBlockedSet G B omega ↔ ¬ ConnToSet G omega Set.univ x B := by
  classical
  simp [mpiBlockedSet]

theorem mpi_not_mem_blockedSet_iff (B : Set V) (omega : ConfigSpace (Sym2 V)) (x : V) :
    x ∉ mpiBlockedSet G B omega ↔ ConnToSet G omega Set.univ x B := by
  rw [← not_iff_not]
  simp only [not_not, mpi_mem_blockedSet_iff]

theorem mpi_not_crossing_iff_mem_blockedSet (o : V) (B : Set V)
    (omega : ConfigSpace (Sym2 V)) :
    omega ∉ mpiCrossingEvent G o B ↔ o ∈ mpiBlockedSet G B omega := by
  rw [mpi_mem_blockedSet_iff]
  rfl


theorem mpi_connToSet_of_adj (B : Set V) (omega : ConfigSpace (Sym2 V))
    {x y : V} (hxy : G.Adj x y) (hopen : omega s(x, y) = true)
    (hy : ConnToSet G omega Set.univ y B) :
    ConnToSet G omega Set.univ x B := by
  obtain ⟨_, b, _, hbB, hyb⟩ := hy
  refine ⟨Set.mem_univ x, b, Set.mem_univ b, hbB, ?_⟩
  have hxy' : ((openSub G omega).induce Set.univ).Adj
      ⟨x, Set.mem_univ x⟩ ⟨y, Set.mem_univ y⟩ := by
    exact ⟨hxy, hopen⟩
  exact hxy'.reachable.trans hyb


theorem mpi_boundary_edge_closed (B : Set V) (omega : ConfigSpace (Sym2 V))
    {S : Finset V} (hS : mpiBlockedSet G B omega = S)
    {x y : V} (hx : x ∈ S) (hy : y ∉ S) (hxy : G.Adj x y) :
    omega s(x, y) = false := by
  have hxb : x ∈ mpiBlockedSet G B omega := hS.symm ▸ hx
  have hyb : y ∉ mpiBlockedSet G B omega := by simpa [hS] using hy
  have hxnot := (mpi_mem_blockedSet_iff G B omega x).mp hxb
  have hyconn := (mpi_not_mem_blockedSet_iff G B omega y).mp hyb
  cases hopen : omega s(x, y) with
  | false => rfl
  | true => exact False.elim (hxnot (mpi_connToSet_of_adj G B omega hxy hopen hyconn))


theorem mpi_le_setOpen (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    omega ≤ setOpen e omega := by
  intro j
  by_cases hje : j = e
  · subst j
    rw [setOpen_self]
    exact Bool.le_true _
  · rw [setOpen_of_ne hje]


theorem mpi_boundary_edge_isPivotal (o : V) (B : Set V)
    (omega : ConfigSpace (Sym2 V)) {S : Finset V}
    (hS : mpiBlockedSet G B omega = S) (ho : o ∈ S)
    {x y : V} (hx : x ∈ S) (hy : y ∉ S) (hxy : G.Adj x y)
    (hox : ConnToSet G omega (S : Set V) o {x}) :
    IsPivotal s(x, y) (mpiCrossingEvent G o B) omega := by
  let e : Sym2 V := s(x, y)
  have hclosed : omega e = false := mpi_boundary_edge_closed G B omega hS hx hy hxy
  have hclosedCfg : setClosed e omega = omega := by
    funext j
    by_cases hje : j = e
    · subst j
      simpa [hclosed] using setClosed_self e omega
    · exact setClosed_of_ne hje omega
  have hnot : setClosed e omega ∉ mpiCrossingEvent G o B := by
    rw [hclosedCfg, mpi_not_crossing_iff_mem_blockedSet]
    simpa [hS] using ho
  have hopenCfg : setOpen e omega ∈ mpiCrossingEvent G o B := by
    have hmono : ConnToSet G (setOpen e omega) (S : Set V) o {x} := by
      obtain ⟨hoS, z, hzS, hz, hconn⟩ := hox
      exact ⟨hoS, z, hzS, hz,
        hconn.mono_config G (mpi_le_setOpen e omega)⟩
    obtain ⟨z, _, hz, p, hpS⟩ := shk_walk_of_connToSet G (setOpen e omega)
      (S : Set V) o {x} hmono
    simp only [Set.mem_singleton_iff] at hz
    subst z
    have hyconn0 : ConnToSet G omega Set.univ y B := by
      apply (mpi_not_mem_blockedSet_iff G B omega y).mp
      simpa [hS] using hy
    have hyconn : ConnToSet G (setOpen e omega) Set.univ y B := by
      obtain ⟨hyU, b, hbU, hbB, hconn⟩ := hyconn0
      exact ⟨hyU, b, hbU, hbB,
        hconn.mono_config G (mpi_le_setOpen e omega)⟩
    obtain ⟨b, _, hbB, q, _⟩ := shk_walk_of_connToSet G (setOpen e omega)
      Set.univ y B hyconn
    have hxyOpen : (openSub G (setOpen e omega)).Adj x y := by
      exact ⟨hxy, by simp [e]⟩
    let walk : (openSub G (setOpen e omega)).Walk o b :=
      p.append (SimpleGraph.Walk.cons hxyOpen q)
    refine ⟨Set.mem_univ o, b, Set.mem_univ b, hbB, ?_⟩
    exact ⟨walk.induce Set.univ (fun _ _ => Set.mem_univ _)⟩
  exact (isPivotal_iff_of_isIncreasing
    (isIncreasing_connEvent G Set.univ o B) omega).2 ⟨hnot, hopenCfg⟩


end Sharpness
end StatMech
