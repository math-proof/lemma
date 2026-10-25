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
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldPercoInhom.Part2
open Finset SimpleGraph Set


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem mpi_internalEdge_mk {S : Set V} {x y : V} (hx : x ∈ S) (hy : y ∈ S) :
    s(x, y) ∈ mpiInternalEdges S := ⟨x, hx, y, hy, rfl⟩

theorem mpi_not_internalEdge_mk_of_right {S : Set V} {x y : V} (hy : y ∉ S) :
    s(x, y) ∉ mpiInternalEdges S := by
  rintro ⟨a, ha, b, hb, hab⟩
  rw [Sym2.eq_iff] at hab
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hy hb
  · exact hy ha


theorem mpi_connWithin_transfer {omega omega' : ConfigSpace (Sym2 V)} {S : Set V}
    (hagree : ∀ e ∈ mpiInternalEdges S, omega e = omega' e)
    {a b : S} (h : ConnWithin G omega S a b) : ConnWithin G omega' S a b := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact SimpleGraph.Reachable.refl _
  | @cons u v t hadj p ih =>
      have hopen' : (openSub G omega').Adj (u : V) (v : V) := by
        refine ⟨hadj.1, ?_⟩
        rw [← hagree s((u : V), (v : V))
          (mpi_internalEdge_mk (S := S) u.2 v.2)]
        exact hadj.2
      exact (show ((openSub G omega').induce S).Adj u v from hopen').reachable.trans ih


theorem mpi_connEvent_determined_internal (S : Finset V) (o x : V) :
    DeterminedBy (connEvent G (S : Set V) o {x}) (mpiInternalEdges (S : Set V)) := by
  intro omega omega' hagree
  constructor
  · rintro ⟨ho, z, hzS, hz, hconn⟩
    exact ⟨ho, z, hzS, hz,
      mpi_connWithin_transfer (omega := omega) (omega' := omega') G
        (fun e he => (hagree e he).symm) hconn⟩
  · rintro ⟨ho, z, hzS, hz, hconn⟩
    exact ⟨ho, z, hzS, hz,
      mpi_connWithin_transfer (omega := omega') (omega' := omega) G
        (fun e he => hagree e he) hconn⟩


theorem mpi_connEventSet_determined_internal (S : Finset V) (o : V) (B : Set V) :
    DeterminedBy (connEvent G (S : Set V) o B) (mpiInternalEdges (S : Set V)) := by
  intro omega omega' hagree
  constructor
  · rintro ⟨ho, z, hzS, hzB, hconn⟩
    exact ⟨ho, z, hzS, hzB,
      mpi_connWithin_transfer (omega := omega) (omega' := omega') G
        (fun e he => (hagree e he).symm) hconn⟩
  · rintro ⟨ho, z, hzS, hzB, hconn⟩
    exact ⟨ho, z, hzS, hzB,
      mpi_connWithin_transfer (omega := omega') (omega' := omega) G
        (fun e he => hagree e he) hconn⟩


theorem mpi_target_not_mem_blockedSet (B : Set V) (omega : ConfigSpace (Sym2 V))
    {b : V} (hb : b ∈ B) : b ∉ mpiBlockedSet G B omega := by
  rw [mpi_not_mem_blockedSet_iff]
  exact ⟨Set.mem_univ b, b, Set.mem_univ b, hb, SimpleGraph.Reachable.refl _⟩


theorem mpi_surfaceEvent_nonempty_disjoint (B : Set V) (S : Finset V)
    (hocc : (mpiSurfaceEvent G B S).Nonempty) :
    Disjoint (S : Set V) B := by
  rw [Set.disjoint_left]
  intro x hxS hxB
  obtain ⟨omega, homega⟩ := hocc
  have hxblocked : x ∈ mpiBlockedSet G B omega := by
    rw [homega]
    exact hxS
  exact mpi_target_not_mem_blockedSet G B omega hxB hxblocked


theorem mpi_outside_connection_walk (B : Set V) (omega : ConfigSpace (Sym2 V))
    {S : Finset V} (hS : mpiBlockedSet G B omega = S) {y : V} (hy : y ∉ S) :
    ∃ b ∈ B, ∃ p : (openSub G omega).Walk y b,
      ∀ z ∈ p.support, z ∉ S := by
  have hyconn : ConnToSet G omega Set.univ y B := by
    apply (mpi_not_mem_blockedSet_iff G B omega y).mp
    simpa [hS] using hy
  obtain ⟨b, _, hbB, p, _⟩ := shk_walk_of_connToSet G omega Set.univ y B hyconn
  refine ⟨b, hbB, p, ?_⟩
  intro z hz hzS
  rw [SimpleGraph.Walk.mem_support_iff_exists_getVert] at hz
  obtain ⟨i, hiz, hi⟩ := hz
  let q : (openSub G omega).Walk z b := (p.drop i).copy hiz rfl
  have hzconn : ConnToSet G omega Set.univ z B := by
    refine ⟨Set.mem_univ z, b, Set.mem_univ b, hbB, ?_⟩
    exact ⟨q.induce Set.univ (fun _ _ => Set.mem_univ _)⟩
  have hzb : z ∈ mpiBlockedSet G B omega := by simpa [hS] using hzS
  exact (mpi_mem_blockedSet_iff G B omega z).mp hzb hzconn


theorem mpi_outside_conn_transfer {B : Set V} {S : Finset V}
    {omega omega' : ConfigSpace (Sym2 V)}
    (hS : mpiBlockedSet G B omega = S)
    (hagree : agreeOn (mpiInternalEdges (S : Set V))ᶜ omega omega')
    {y : V} (hy : y ∉ S) : ConnToSet G omega' Set.univ y B := by
  obtain ⟨b, hbB, p, hpout⟩ := mpi_outside_connection_walk G B omega hS hy
  have hpAgree : agreeOn {e : Sym2 V | e ∈ p.edges} omega omega' := by
    intro e he
    apply hagree
    induction e using Sym2.ind with
    | _ a c =>
        exact mpi_not_internalEdge_mk_of_right
          (hpout c (p.snd_mem_support_of_mem_edges he))
  let q : (openSub G omega').Walk y b :=
    p.transfer (openSub G omega') (shk_edges_subset_openSub G omega omega' p hpAgree)
  refine ⟨Set.mem_univ y, b, Set.mem_univ b, hbB, ?_⟩
  exact ⟨q.induce Set.univ (fun _ _ => Set.mem_univ _)⟩


theorem mpi_inside_not_conn_of_exterior_agree {B : Set V} {S : Finset V}
    {omega omega' : ConfigSpace (Sym2 V)}
    (hS : mpiBlockedSet G B omega = S)
    (hagree : agreeOn (mpiInternalEdges (S : Set V))ᶜ omega omega')
    {x : V} (hx : x ∈ S) : ¬ ConnToSet G omega' Set.univ x B := by
  intro hxconn
  obtain ⟨b, _, hbB, p, _⟩ := shk_walk_of_connToSet G omega' Set.univ x B hxconn
  have hbS : b ∉ (S : Set V) := by
    intro hbSin
    have hbb : b ∈ mpiBlockedSet G B omega := by simpa [hS] using hbSin
    exact (mpi_target_not_mem_blockedSet G B omega hbB) hbb
  obtain ⟨a, y, haS, hyS, hay, htriple⟩ :=
    shk_firstExit_triple G omega' Set.univ (S : Set V) B x b
      (by exact_mod_cast hx) hbB hbS p.bypass p.bypass_isPath (fun _ _ => Set.mem_univ _)
  have hinter := disjointOccurrence_subset_inter _ _ htriple
  have hinner := disjointOccurrence_subset_inter _ _ hinter.2
  have hopen' : omega' s(a, y) = true := hinner.1
  have hopen : omega s(a, y) = true := by
    exact (hagree s(a, y) (mpi_not_internalEdge_mk_of_right hyS)).symm.trans hopen'
  have hyconn : ConnToSet G omega Set.univ y B := by
    apply (mpi_not_mem_blockedSet_iff G B omega y).mp
    simpa [hS] using hyS
  have haconn := mpi_connToSet_of_adj G B omega hay hopen hyconn
  have hablocked : a ∈ mpiBlockedSet G B omega := by simpa [hS] using haS
  exact (mpi_mem_blockedSet_iff G B omega a).mp hablocked haconn


theorem mpi_surfaceEvent_determined_exterior (B : Set V) (S : Finset V) :
    DeterminedBy (mpiSurfaceEvent G B S) (mpiInternalEdges (S : Set V))ᶜ := by
  intro omega omega' hagree
  have transfer : ∀ {eta eta' : ConfigSpace (Sym2 V)},
      agreeOn (mpiInternalEdges (S : Set V))ᶜ eta eta' →
      mpiBlockedSet G B eta = S → mpiBlockedSet G B eta' = S := by
    intro eta eta' hagree' hsurf
    ext z
    rw [mpi_mem_blockedSet_iff]
    change (¬ ConnToSet G eta' Set.univ z B) ↔ z ∈ S
    constructor
    · intro hznot
      by_contra hzS
      have hzconn : ConnToSet G eta' Set.univ z B :=
        mpi_outside_conn_transfer G hsurf hagree' hzS
      exact hznot hzconn
    · intro hzS
      exact mpi_inside_not_conn_of_exterior_agree G hsurf hagree' hzS
  constructor
  · exact transfer hagree
  · exact transfer (fun e he => (hagree e he).symm)


theorem mpi_conn_surface_factor (beta : ℝ) (J : Sym2 V → ℝ)
    (B : Set V) (S : Finset V) (o x : V) :
    wprob (shk_edgeLaw beta J)
        (connEvent G (S : Set V) o {x} ∩ mpiSurfaceEvent G B S) =
      wprob (shk_edgeLaw beta J) (connEvent G (S : Set V) o {x}) *
        wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
  exact wprob_inter_eq_mul_of_determined _ _ disjoint_compl_right
    (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J)
    (mpi_connEvent_determined_internal G S o x)
    (mpi_surfaceEvent_determined_exterior G B S)


end Sharpness
end StatMech
