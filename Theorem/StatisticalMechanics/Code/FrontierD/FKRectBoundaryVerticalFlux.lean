/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectBoundaryVerticalFlux.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectBlackOrbitWindingGeometry.Part10
import Theorem.StatisticalMechanics.Code.FrontierD.FKMedialLoopVerticalWinding.Part3
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectZeroTurnDevelopedAnchor.Part11
open Equiv Finset SimpleGraph
open StatMech.Onsager StatMech.Onsager.BaseCase


namespace StatMech.FrontierD

noncomputable section

@[simp] theorem finitePeriodicSucc_svFinLast {N : Nat} (hN : 0 < N) :
    finitePeriodicSucc hN (svFinLast hN) = (⟨0, hN⟩ : Fin N) := by
  apply Fin.ext
  simp [finitePeriodicSucc, svFinLast, Nat.sub_add_cancel hN]

theorem not_even_svFinLast_of_even {N : Nat} (hN : 0 < N)
    (heven : Even N) : ¬ Even (svFinLast hN).val := by
  simp only [svFinLast, Fin.val_mk]
  rw [Nat.even_sub hN]
  simp [heven]

theorem finZero_ne_svFinLast {N : Nat} (hN : 1 < N) :
    (⟨0, Nat.zero_lt_of_lt hN⟩ : Fin N) ≠
      svFinLast (Nat.zero_lt_of_lt hN) := by
  intro h
  have hv := congrArg Fin.val h
  simp only [svFinLast, Fin.val_mk] at hv
  omega


end
end StatMech.FrontierD
