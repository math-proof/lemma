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
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldPercoInhom.Part3
open Finset SimpleGraph Set


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem mpi_wprob_crossing_compl_eq_sum_surfaces
    (phi : Sym2 V → Bool → ℝ) (hphi : ∀ e, phi e false + phi e true = 1)
    (o : V) (B : Set V) :
    wprob phi (mpiCrossingEvent G o B)ᶜ =
      ∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S),
        wprob phi (mpiSurfaceEvent G B S) := by
  classical
  unfold wprob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega _
  by_cases hcross : omega ∈ mpiCrossingEvent G o B
  · rw [Set.indicator_of_notMem (by simpa using hcross)]
    rw [zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro S hS
    rw [Set.indicator_of_notMem]
    · exact zero_mul _
    · intro hsurf
      have hoS : o ∈ S := (Finset.mem_filter.mp hS).2
      have hblocked : mpiBlockedSet G B omega = S := hsurf
      have hob : o ∈ mpiBlockedSet G B omega := hblocked.symm ▸ hoS
      exact (mpi_not_crossing_iff_mem_blockedSet G o B omega).mpr hob hcross
  · rw [Set.indicator_of_mem (by simpa using hcross), one_mul]
    let S0 := mpiBlockedSet G B omega
    have hoS0 : o ∈ S0 := (mpi_not_crossing_iff_mem_blockedSet G o B omega).mp hcross
    have hS0mem : S0 ∈ (Finset.univ.filter fun S : Finset V => o ∈ S) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hoS0⟩
    symm
    calc
      (∑ S ∈ (Finset.univ.filter fun S : Finset V => o ∈ S),
          (mpiSurfaceEvent G B S).indicator (fun _ => (1 : ℝ)) omega *
            pweight phi omega) =
          (mpiSurfaceEvent G B S0).indicator (fun _ => (1 : ℝ)) omega *
            pweight phi omega := by
        apply Finset.sum_eq_single S0
        · intro S hSmem hSne
          rw [Set.indicator_of_notMem]
          · exact zero_mul _
          · exact fun heq => hSne heq.symm
        · exact fun hnot => False.elim (hnot hS0mem)
      _ = pweight phi omega := by
        rw [Set.indicator_of_mem (show omega ∈ mpiSurfaceEvent G B S0 from rfl), one_mul]


theorem mpi_wprob_compl (phi : Sym2 V → Bool → ℝ)
    (hphi : ∀ e, phi e false + phi e true = 1)
    (A : Set (ConfigSpace (Sym2 V))) :
    wprob phi Aᶜ = 1 - wprob phi A := by
  have h := wprob_add_compl phi hphi A
  linarith


theorem mpi_perSurface_eq_phi (beta : ℝ) (J : Sym2 V → ℝ)
    (o : V) (B : Set V) (S : Finset V) :
    (∑ q ∈ shk_boundaryPairs G S,
      (1 - Real.exp (-beta * J s(q.1, q.2))) *
        wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) =
      mpiPhi G beta J o S * wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) := by
  unfold mpiPhi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [mpi_conn_surface_factor G beta J B S o q.1]
  ring


theorem mpi_openWeight_div_beta_le (beta Je : ℝ)
    (hbeta : 0 < beta) (hJe : 0 ≤ Je) :
    (1 / beta) * (1 - Real.exp (-beta * Je)) ≤ Je := by
  have ht := Real.add_one_le_exp (-beta * Je)
  have hp : 1 - Real.exp (-beta * Je) ≤ beta * Je := by linarith
  rw [one_div, inv_mul_le_iff₀ hbeta]
  simpa [mul_comm] using hp


theorem mpi_phi_surface_le_boundaryJ (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (S : Finset V) :
    (1 / beta) * mpiPhi G beta J o S *
        wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) ≤
      ∑ q ∈ shk_boundaryPairs G S,
        J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) := by
  rw [show (1 / beta) * mpiPhi G beta J o S *
      wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S) =
        (1 / beta) * (mpiPhi G beta J o S *
          wprob (shk_edgeLaw beta J) (mpiSurfaceEvent G B S)) by ring,
    ← mpi_perSurface_eq_phi G beta J o B S, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q _
  have hprob : 0 ≤ wprob (shk_edgeLaw beta J)
      (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) :=
    wprob_nonneg (fun e b => shk_edgeLaw_nonneg beta J hbeta.le hJ e b) _
  have hw := mpi_openWeight_div_beta_le beta (J s(q.1, q.2)) hbeta (hJ _)
  calc
    (1 / beta) *
        ((1 - Real.exp (-beta * J s(q.1, q.2))) *
          wprob (shk_edgeLaw beta J)
            (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S)) =
      ((1 / beta) * (1 - Real.exp (-beta * J s(q.1, q.2)))) *
        wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) := by ring
    _ ≤ J s(q.1, q.2) * wprob (shk_edgeLaw beta J)
          (connEvent G (S : Set V) o {q.1} ∩ mpiSurfaceEvent G B S) :=
      mul_le_mul_of_nonneg_right hw hprob


end Sharpness
end StatMech
