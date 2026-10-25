/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Def.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness.Part5
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

open StatMech.Lattice StatMech.Ising StatMech.FrontierC


lemma blockInteriorStateEquiv_apply
    (eta : ConfigSpace (Site 1)) (r m : ℕ)
    (tau : {x // x ∈ box 1 (r + m)} → Bool)
    (i : Fin (2 * r + 1)) :
    blockInteriorStateEquiv r m tau ⟨m + i.val, by omega⟩ =
      boolTransferState
        (glue eta tau (site1 (-(r : ℤ) + (i.val : ℤ)))) := by
  rw [blockInteriorStateEquiv]
  change pathCastEquiv (Fin 2) (by omega)
    (interiorStateEquiv (r + m) tau) ⟨m + i.val, by omega⟩ = _
  rw [pathCastEquiv_apply]
  rw [interiorStateEquiv_apply eta]
  unfold fvPathState
  congr 3
  simp only [Fin.val_cast]
  push_cast
  ring

lemma pathContainsWord_block_iff
    (eta : ConfigSpace (Site 1)) (r m : ℕ)
    (tau : {x // x ∈ box 1 (r + m)} → Bool)
    (p : Fin (2 * r + 1) → Fin 2) :
    pathContainsWord (m := m) (n := m) p (blockInteriorStateEquiv r m tau) ↔
      glue eta tau ∈ blockStateEvent r p := by
  constructor
  · intro hp i
    exact (blockInteriorStateEquiv_apply eta r m tau i).symm.trans (hp i)
  · intro hp i
    exact (blockInteriorStateEquiv_apply eta r m tau i).trans (hp i)

theorem sum_fvTransferProduct_block_eq_matrix_pow
    (eta : ConfigSpace (Site 1)) (r m : ℕ) (beta h : ℝ)
    (p : Fin (2 * r + 1) → Fin 2) :
    (∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
      if glue eta tau ∈ blockStateEvent r p then
        fvTransferProduct eta (r + m) tau beta h else 0) =
      (isingTransferReal beta (beta * h) ^ (m + 1))
          (fvLeftBoundaryState eta (r + m)) (p 0) *
        fixedWordProduct (isingTransferReal beta (beta * h)) p *
          (isingTransferReal beta (beta * h) ^ (m + 1))
            (p (Fin.last (2 * r))) (fvRightBoundaryState eta (r + m)) := by
  let A := isingTransferReal beta (beta * h)
  calc
    _ = ∑ tau : {x // x ∈ box 1 (r + m)} → Bool,
        if pathContainsWord (m := m) (n := m) p (blockInteriorStateEquiv r m tau) then
          openMatrixProduct A (fvLeftBoundaryState eta (r + m))
            (fvRightBoundaryState eta (r + m)) (blockInteriorStateEquiv r m tau) else 0 := by
      apply Finset.sum_congr rfl
      intro tau htau
      simp only [pathContainsWord_block_iff eta]
      by_cases hp : glue eta tau ∈ blockStateEvent r p
      · simp only [hp, if_true]
        rw [blockInteriorStateEquiv]
        change fvTransferProduct eta (r + m) tau beta h =
          openMatrixProduct A _ _
            (pathCastEquiv (Fin 2)
              (show 2 * (r + m) + 1 = m + (m + 2 * r) + 1 by omega)
              (interiorStateEquiv (r + m) tau))
        rw [openMatrixProduct_pathCast]
        exact fvTransferProduct_eq_openMatrixProduct eta (r + m) tau beta h
      · simp [hp]
    _ = ∑ q : Fin (m + (m + 2 * r) + 1) → Fin 2,
        if pathContainsWord (m := m) (n := m) p q then
          openMatrixProduct A (fvLeftBoundaryState eta (r + m))
            (fvRightBoundaryState eta (r + m)) q else 0 :=
      by
        simpa only using Equiv.sum_comp (blockInteriorStateEquiv r m)
          (fun q => if pathContainsWord (m := m) (n := m) p q then
            openMatrixProduct A (fvLeftBoundaryState eta (r + m))
              (fvRightBoundaryState eta (r + m)) q else 0)
    _ = _ := sum_openMatrixProduct_fixedWord A
      (fvLeftBoundaryState eta (r + m)) (fvRightBoundaryState eta (r + m))
      (2 * r) m m p

end StatMech.FrontierB
