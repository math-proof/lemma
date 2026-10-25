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
import Def.StatisticalMechanics.Code.Sharpness.MeanfieldPercoInhom.Part5
open Finset SimpleGraph Set


namespace StatMech

namespace Sharpness

open ConfigSpace

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem mpi_pweight_eq_edge_mul_off (beta : ℝ) (J : Sym2 V → ℝ)
    (e : Sym2 V) (omega : ConfigSpace (Sym2 V)) :
    pweight (shk_edgeLaw beta J) omega =
      shk_edgeLaw beta J e (omega e) * mpiWeightOff beta J e omega := by
  unfold pweight mpiWeightOff
  exact (Finset.mul_prod_erase Finset.univ
    (fun j => shk_edgeLaw beta J j (omega j)) (Finset.mem_univ e)).symm

theorem mpi_weightOff_congr (beta : ℝ) (J : Sym2 V → ℝ) (e : Sym2 V)
    {omega omega' : ConfigSpace (Sym2 V)}
    (h : ∀ j, j ≠ e → omega j = omega' j) :
    mpiWeightOff beta J e omega = mpiWeightOff beta J e omega' := by
  unfold mpiWeightOff
  apply Finset.prod_congr rfl
  intro j hj
  rw [Finset.mem_erase] at hj
  rw [h j hj.1]


theorem mpi_hasDerivAt_pweight (J : Sym2 V → ℝ) (beta : ℝ)
    (omega : ConfigSpace (Sym2 V)) :
    HasDerivAt (fun b => pweight (shk_edgeLaw b J) omega)
      (∑ e, mpiWeightOff beta J e omega *
        (if omega e then J e * Real.exp (-(beta * J e))
          else -(J e * Real.exp (-(beta * J e))))) beta := by
  unfold pweight mpiWeightOff shk_edgeLaw
  have h := HasDerivAt.fun_finsetProd (u := (Finset.univ : Finset (Sym2 V)))
    (f := fun e b => if omega e then 1 - Real.exp (-b * J e) else Real.exp (-b * J e))
    (f' := fun e => if omega e then J e * Real.exp (-(beta * J e))
      else -(J e * Real.exp (-(beta * J e))))
    (x := beta) (fun e _ => by
      simpa [FK.betaParams] using FK.hasDerivAt_betaFactor J omega e beta)
  simpa [smul_eq_mul] using h


theorem mpi_perEdge_beta_pivotal (beta : ℝ) (J : Sym2 V → ℝ)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A) (e : Sym2 V) :
    (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
      (mpiWeightOff beta J e omega *
        (if omega e then J e * Real.exp (-(beta * J e))
          else -(J e * Real.exp (-(beta * J e)))))) =
      J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e A) := by
  unfold wprob
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
      (fun omega => A.indicator (fun _ => (1 : ℝ)) omega *
        (mpiWeightOff beta J e omega *
          (if omega e then J e * Real.exp (-(beta * J e))
            else -(J e * Real.exp (-(beta * J e))))))]
  rw [← Equiv.sum_comp (Equiv.funSplitAt e Bool).symm
      (fun omega => (mpiPivotalClosed e A).indicator (fun _ => (1 : ℝ)) omega *
        pweight (shk_edgeLaw beta J) omega)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type,
    Fintype.sum_bool, Fintype.sum_bool,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro eta _
  let omegaT := (Equiv.funSplitAt e Bool).symm (true, eta)
  let omegaF := (Equiv.funSplitAt e Bool).symm (false, eta)
  change A.indicator (fun _ => (1 : ℝ)) omegaT *
      (mpiWeightOff beta J e omegaT *
        (if omegaT e then J e * Real.exp (-(beta * J e))
          else -(J e * Real.exp (-(beta * J e))))) +
      A.indicator (fun _ => (1 : ℝ)) omegaF *
      (mpiWeightOff beta J e omegaF *
        (if omegaF e then J e * Real.exp (-(beta * J e))
          else -(J e * Real.exp (-(beta * J e))))) =
    J e * ((mpiPivotalClosed e A).indicator (fun _ => (1 : ℝ)) omegaT *
      pweight (shk_edgeLaw beta J) omegaT +
      (mpiPivotalClosed e A).indicator (fun _ => (1 : ℝ)) omegaF *
      pweight (shk_edgeLaw beta J) omegaF)
  have ht : omegaT e = true := by
    simp [omegaT, Equiv.funSplitAt, Equiv.piSplitAt]
  have hf : omegaF e = false := by
    simp [omegaF, Equiv.funSplitAt, Equiv.piSplitAt]
  have hsame : ∀ j, j ≠ e → omegaT j = omegaF j := by
    intro j hj
    simp [omegaT, omegaF, Equiv.funSplitAt, Equiv.piSplitAt, hj]
  have hto : setOpen e omegaT = omegaT := by
    funext j
    by_cases hje : j = e
    · subst j
      rw [setOpen_self, ht]
    · rw [setOpen_of_ne hje]
  have htc : setClosed e omegaT = omegaF := by
    funext j
    by_cases hje : j = e
    · subst j
      rw [setClosed_self, hf]
    · rw [setClosed_of_ne hje, hsame j hje]
  have hoff : mpiWeightOff beta J e omegaT = mpiWeightOff beta J e omegaF :=
    mpi_weightOff_congr beta J e hsame
  have hpiv : IsPivotal e A omegaT ↔ (omegaF ∉ A ∧ omegaT ∈ A) := by
    rw [isPivotal_iff_of_isIncreasing hA, hto, htc]
  have hpivEq : IsPivotal e A omegaT ↔ IsPivotal e A omegaF := by
    apply isPivotal_congr
    intro j hj
    exact hsame j hj
  have hwF : pweight (shk_edgeLaw beta J) omegaF =
      Real.exp (-(beta * J e)) * mpiWeightOff beta J e omegaF := by
    rw [mpi_pweight_eq_edge_mul_off beta J e omegaF]
    simp [shk_edgeLaw, hf]
  have hTnot : omegaT ∉ mpiPivotalClosed e A := by
    intro h
    exact Bool.noConfusion (ht.symm.trans h.2)
  by_cases hmt : omegaT ∈ A <;> by_cases hmf : omegaF ∈ A
  · have hnp : ¬ IsPivotal e A omegaT := by rw [hpiv]; tauto
    have hFnot : omegaF ∉ mpiPivotalClosed e A := by
      intro h
      exact (hpivEq.not.mp hnp) h.1
    simp [Set.indicator_of_mem hmt, Set.indicator_of_mem hmf,
      Set.indicator_of_notMem hTnot, Set.indicator_of_notMem hFnot, ht, hf, hoff]
  · have hp : IsPivotal e A omegaT := hpiv.mpr ⟨hmf, hmt⟩
    have hFmem : omegaF ∈ mpiPivotalClosed e A := ⟨hpivEq.mp hp, hf⟩
    rw [Set.indicator_of_mem hmt, Set.indicator_of_notMem hmf,
      Set.indicator_of_notMem hTnot, Set.indicator_of_mem hFmem]
    simp only [ht, hf, if_true, if_false, one_mul, zero_mul, zero_add, hwF]
    rw [hoff]
    ring
  · exfalso
    have hle : omegaF ≤ omegaT := by
      intro j
      by_cases hje : j = e
      · subst j
        rw [hf, ht]
        exact bot_le
      · rw [hsame j hje]
    exact hmt (hA hle hmf)
  · have hnp : ¬ IsPivotal e A omegaT := by rw [hpiv]; tauto
    have hFnot : omegaF ∉ mpiPivotalClosed e A := by
      intro h
      exact (hpivEq.not.mp hnp) h.1
    simp [Set.indicator_of_notMem hmt, Set.indicator_of_notMem hmf,
      Set.indicator_of_notMem hTnot, Set.indicator_of_notMem hFnot, ht, hf]


theorem mpi_hasDerivAt_wprob (beta : ℝ) (J : Sym2 V → ℝ)
    (A : Set (ConfigSpace (Sym2 V))) (hA : IsIncreasing A) :
    HasDerivAt (fun b => wprob (shk_edgeLaw b J) A)
      (∑ e, J e * wprob (shk_edgeLaw beta J) (mpiPivotalClosed e A)) beta := by
  change HasDerivAt
    (fun b => ∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
      pweight (shk_edgeLaw b J) omega) _ beta
  have hd := HasDerivAt.fun_sum (u := (Finset.univ : Finset (ConfigSpace (Sym2 V))))
    (fun omega _ => (mpi_hasDerivAt_pweight J beta omega).const_mul
      (A.indicator (fun _ => (1 : ℝ)) omega))
  refine hd.congr_deriv ?_
  rw [show (∑ omega, A.indicator (fun _ => (1 : ℝ)) omega *
        (∑ e, mpiWeightOff beta J e omega *
          (if omega e then J e * Real.exp (-(beta * J e))
            else -(J e * Real.exp (-(beta * J e)))))) =
      ∑ omega, ∑ e, A.indicator (fun _ => (1 : ℝ)) omega *
        (mpiWeightOff beta J e omega *
          (if omega e then J e * Real.exp (-(beta * J e))
            else -(J e * Real.exp (-(beta * J e))))) by
      apply Finset.sum_congr rfl
      intro omega _
      rw [Finset.mul_sum], Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  exact mpi_perEdge_beta_pivotal beta J A hA e


theorem mpi_meanfield_perco (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S → m ≤ mpiPhi G beta J o S) :
    HasDerivAt
        (fun b => wprob (shk_edgeLaw b J) (mpiCrossingEvent G o B))
        (∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B))) beta ∧
      (1 / beta) * m *
          (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
        ∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  refine ⟨mpi_hasDerivAt_wprob beta J (mpiCrossingEvent G o B)
    (isIncreasing_connEvent G Set.univ o B), ?_⟩
  have hs := mpi_surface_reassembly G beta J hbeta hJ o B m hm
  apply hs.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact fun e he => Finset.mem_univ e
  · intro e _ _
    exact mul_nonneg (hJ e)
      (wprob_nonneg (fun j b => shk_edgeLaw_nonneg beta J hbeta.le hJ j b) _)


theorem mpi_meanfield_perco_of_nonempty (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S →
      (mpiSurfaceEvent G B S).Nonempty → m ≤ mpiPhi G beta J o S) :
    HasDerivAt
        (fun b => wprob (shk_edgeLaw b J) (mpiCrossingEvent G o B))
        (∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B))) beta ∧
      (1 / beta) * m *
          (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
        ∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  refine ⟨mpi_hasDerivAt_wprob beta J (mpiCrossingEvent G o B)
    (isIncreasing_connEvent G Set.univ o B), ?_⟩
  have hs := mpi_surface_reassembly_of_nonempty G beta J hbeta hJ o B m hm
  apply hs.trans
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact fun e he => Finset.mem_univ e
  · intro e _ _
    exact mul_nonneg (hJ e)
      (wprob_nonneg (fun j b => shk_edgeLaw_nonneg beta J hbeta.le hJ j b) _)


theorem mpi_meanfield_perco_of_disjoint (beta : ℝ) (J : Sym2 V → ℝ)
    (hbeta : 0 < beta) (hJ : ∀ e, 0 ≤ J e)
    (o : V) (B : Set V) (m : ℝ)
    (hm : ∀ S : Finset V, o ∈ S → Disjoint (S : Set V) B →
      m ≤ mpiPhi G beta J o S) :
    HasDerivAt
        (fun b => wprob (shk_edgeLaw b J) (mpiCrossingEvent G o B))
        (∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B))) beta ∧
      (1 / beta) * m *
          (1 - wprob (shk_edgeLaw beta J) (mpiCrossingEvent G o B)) ≤
        ∑ e, J e * wprob (shk_edgeLaw beta J)
          (mpiPivotalClosed e (mpiCrossingEvent G o B)) := by
  apply mpi_meanfield_perco_of_nonempty G beta J hbeta hJ o B m
  intro S hoS hocc
  exact hm S hoS (mpi_surfaceEvent_nonempty_disjoint G B S hocc)

end Sharpness
end StatMech
