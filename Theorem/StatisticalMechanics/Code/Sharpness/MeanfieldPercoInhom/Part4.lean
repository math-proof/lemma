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
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldPercoInhom.Part4
open Finset SimpleGraph Set


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem mpi_setClosed_eq_of_false {e : Sym2 V} {omega : ConfigSpace (Sym2 V)}
    (he : omega e = false) : setClosed e omega = omega := by
  funext j
  by_cases hje : j = e
  · subst j
    simpa [he] using setClosed_self e omega
  · exact setClosed_of_ne hje omega


theorem mpi_pivotalClosed_subset_compl {e : Sym2 V}
    {A : Set (ConfigSpace (Sym2 V))} (hA : IsIncreasing A) :
    mpiPivotalClosed e A ⊆ Aᶜ := by
  intro omega h
  obtain ⟨hpiv, he⟩ := h
  have hnot := (isPivotal_iff_of_isIncreasing hA omega).mp hpiv |>.1
  rw [mpi_setClosed_eq_of_false he] at hnot
  exact hnot


theorem mpi_conn_surface_subset_pivotalClosed (o : V) (B : Set V)
    (S : Finset V) (ho : o ∈ S) {q : V × V}
    (hq : q ∈ shk_boundaryPairs G S) :
    connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S ⊆
      mpiPivotalClosed s(q.1, q.2) (mpiCrossingEvent G o B) := by
  rintro omega ⟨hconn, hsurf⟩
  obtain ⟨hx, hy, hadj⟩ := (shk_mem_boundaryPairs G S).mp hq
  have hpiv := mpi_boundary_edge_isPivotal G o B omega hsurf ho hx hy hadj hconn
  have hclosed := mpi_boundary_edge_closed G B omega hsurf hx hy hadj
  exact ⟨hpiv, hclosed⟩


theorem mpi_wprob_eq_sum_inter_surfaces
    (phi : Sym2 V → Bool → ℝ) (o : V) (B : Set V)
    (C : Set (ConfigSpace (Sym2 V))) (hC : C ⊆ (mpiCrossingEvent G o B)ᶜ) :
    wprob phi C =
      ∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S),
        wprob phi (C ∩ mpiSurfaceEvent G B S) := by
  classical
  unfold wprob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases homega : omega ∈ C
  · rw [Set.indicator_of_mem homega, one_mul]
    have hncross : omega ∉ mpiCrossingEvent G o B := hC homega
    let S0 := mpiBlockedSet G B omega
    have hoS0 : o ∈ S0 := (mpi_not_crossing_iff_mem_blockedSet G o B omega).mp hncross
    have hS0mem : S0 ∈ (Finset.univ.filter fun S : Finset V => o ∈ S) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoS0⟩
    symm
    calc
      (∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S),
          (C ∩ mpiSurfaceEvent G B S).indicator (fun _ => (1 : ℝ)) omega *
            pweight phi omega) =
          (C ∩ mpiSurfaceEvent G B S0).indicator (fun _ => (1 : ℝ)) omega *
            pweight phi omega := by
        apply Finset.sum_eq_single S0
        · intro S _ hSne
          rw [Set.indicator_of_notMem]
          · exact zero_mul _
          · rintro ⟨_, heq⟩
            exact hSne heq.symm
        · exact fun hnot => False.elim (hnot hS0mem)
      _ = pweight phi omega := by
        have hmem : omega ∈ C ∩ mpiSurfaceEvent G B S0 :=
          ⟨homega, show mpiBlockedSet G B omega = S0 from rfl⟩
        rw [Set.indicator_of_mem hmem, one_mul]
  · rw [Set.indicator_of_notMem homega, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro S _
    rw [Set.indicator_of_notMem]
    · exact zero_mul _
    · exact fun h => homega h.1


theorem mpi_boundaryJ_le_edgePivotal_surface (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (S : Finset V) (ho : o ∈ S) :
    (∑ q ∈ shk_boundaryPairs G S,
        J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) ≤
      ∑ e ∈ G.edgeFinset,
        J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S) := by
  let f : Sym2 V → ℝ := fun e => J e * wprob (shk_edgeLaw beta J)
    (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S)
  have hinj : Set.InjOn (fun q : V × V => s(q.1, q.2))
      (shk_boundaryPairs G S : Set (V × V)) := by
    intro q hq r hr hqr
    obtain ⟨qx, qy, _⟩ := (shk_mem_boundaryPairs G S).mp hq
    obtain ⟨rx, ry, _⟩ := (shk_mem_boundaryPairs G S).mp hr
    rw [Sym2.eq_iff] at hqr
    rcases hqr with h | h
    · exact Prod.ext h.1 h.2
    · have : q.2 ∈ S := by rw [h.2]; exact rx
      exact False.elim (qy this)
  have himage : (shk_boundaryPairs G S).image (fun q => s(q.1, q.2)) ⊆
      G.edgeFinset := by
    intro e he
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp he
    rw [SimpleGraph.mem_edgeFinset]
    exact (shk_mem_boundaryPairs G S).mp hq |>.2.2
  calc
    (∑ q ∈ shk_boundaryPairs G S,
        J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) ≤
      ∑ q ∈ shk_boundaryPairs G S, f s(q.1, q.2) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left _ (hJ _)
        apply wprob_mono (fun e b => shk_edgeLaw_nonneg beta J hbeta.le hJ e b)
        intro omega h
        exact ⟨mpi_conn_surface_subset_pivotalClosed G o B S ho hq h, h.2⟩
    _ = ∑ e ∈ (shk_boundaryPairs G S).image (fun q => s(q.1, q.2)), f e := by
        symm
        exact Finset.sum_image hinj
    _ ≤ ∑ e ∈ G.edgeFinset, f e := by
        apply Finset.sum_le_sum_of_subset_of_nonneg himage
        intro e _ _
        exact mul_nonneg (hJ e)
          (wprob_nonneg (fun j b => shk_edgeLaw_nonneg beta J hbeta.le hJ j b) _)


theorem mpi_surface_reassembly (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S → m ≤ mpiPhi G beta J o S) :
    (1 / beta) * m *
        (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
      ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J)
        (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  let P : Finset (Finset V) := Finset.univ.filter fun S => o ∈ S
  have hmass : 1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B) =
      ∑ S ∈ P, wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
    rw [← mpi_wprob_compl (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J)]
    exact mpi_wprob_crossing_compl_eq_sum_surfaces G
      (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J) o B
  calc
    (1 / beta) * m *
        (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) =
      ∑ S ∈ P, (1 / beta) * m *
        wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
          rw [hmass, Finset.mul_sum]
    _ ≤ ∑ S ∈ P, ∑ e ∈ G.edgeFinset,
        J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S) := by
      apply Finset.sum_le_sum
      intro S hS
      have hoS : o ∈ S := (Finset.mem_filter.mp hS).2
      have hsurf : 0 ≤ wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) :=
        wprob_nonneg (fun e b => shk_edgeLaw_nonneg beta J hbeta.le hJ e b) _
      calc
        (1 / beta) * m * wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) ≤
          (1 / beta) * mpiPhi G beta J o S *
            wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
              apply mul_le_mul_of_nonneg_right _ hsurf
              exact mul_le_mul_of_nonneg_left (hm S hoS) (by positivity)
        _ ≤ ∑ q ∈ shk_boundaryPairs G S,
            J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
              (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) :=
          mpi_phi_surface_le_boundaryJ G beta J hbeta hJ o B S
        _ ≤ ∑ e ∈ G.edgeFinset,
            J e * wprob (shk_edgeLaw beta J)
              (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S) :=
          mpi_boundaryJ_le_edgePivotal_surface G beta J hbeta hJ o B S hoS
    _ = ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J)
        (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.mul_sum]
      congr 1
      symm
      exact mpi_wprob_eq_sum_inter_surfaces G (shk_edgeLaw beta J) o B
        (mpiPivotalClosed e (mpiCrossingEvent G o B))
        (mpi_pivotalClosed_subset_compl (isIncreasing_connEvent G Set.univ o B))


theorem mpi_surface_reassembly_of_nonempty (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S →
      (mpiSurfaceEvent G B S).Nonempty → m ≤ mpiPhi G beta J o S) :
    (1 / beta) * m *
        (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
      ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J)
        (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  let P : Finset (Finset V) := Finset.univ.filter fun S => o ∈ S
  have hmass : 1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B) =
      ∑ S ∈ P, wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
    rw [← mpi_wprob_compl (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J)]
    exact mpi_wprob_crossing_compl_eq_sum_surfaces G
      (shk_edgeLaw beta J) (shk_edgeLaw_sum_one beta J) o B
  calc
    (1 / beta) * m *
        (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) =
      ∑ S ∈ P, (1 / beta) * m *
        wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
          rw [hmass, Finset.mul_sum]
    _ ≤ ∑ S ∈ P, ∑ e ∈ G.edgeFinset,
        J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩ mpiSurfaceEvent G B S) := by
      apply Finset.sum_le_sum
      intro S hS
      have hoS : o ∈ S := (Finset.mem_filter.mp hS).2
      by_cases hocc : (mpiSurfaceEvent G B S).Nonempty
      · have hsurf : 0 ≤ wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) :=
          wprob_nonneg (fun e b => shk_edgeLaw_nonneg beta J hbeta.le hJ e b) _
        calc
          (1 / beta) * m * wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) ≤
              (1 / beta) * mpiPhi G beta J o S *
                wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
            apply mul_le_mul_of_nonneg_right _ hsurf
            exact mul_le_mul_of_nonneg_left (hm S hoS hocc) (by positivity)
          _ ≤ ∑ q ∈ shk_boundaryPairs G S,
              J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
                (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) :=
            mpi_phi_surface_le_boundaryJ G beta J hbeta hJ o B S
          _ ≤ ∑ e ∈ G.edgeFinset,
              J e * wprob (shk_edgeLaw beta J)
                (mpiPivotalClosed e (mpiCrossingEvent G o B) ∩
                  mpiSurfaceEvent G B S) :=
            mpi_boundaryJ_le_edgePivotal_surface G beta J hbeta hJ o B S hoS
      · have hempty : mpiSurfaceEvent G B S = ∅ :=
          Set.not_nonempty_iff_eq_empty.mp hocc
        rw [hempty]
        simp [wprob]
    _ = ∑ e ∈ G.edgeFinset, J e * wprob (shk_edgeLaw beta J)
        (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [← Finset.mul_sum]
      congr 1
      symm
      exact mpi_wprob_eq_sum_inter_surfaces G (shk_edgeLaw beta J) o B
        (mpiPivotalClosed e (mpiCrossingEvent G o B))
        (mpi_pivotalClosed_subset_compl (isIncreasing_connEvent G Set.univ o B))


end Sharpness
end StatMech
