/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Universality.HexLattice.Part11
import Theorem.StatisticalMechanics.Code.Universality.HexConnEndgame
import Def.StatisticalMechanics.Code.Universality.HexBridge.Part3


namespace StatMech.Universality

open Filter Topology

open scoped Topology BigOperators


namespace HexColumnEmb

variable {W I : Type*} (E : HexColumnEmb W I)


theorem fiberSum_summable (hZ : Summable E.wtSAW) :
    Summable E.fiberSum := by
  
  have htot : Summable (fun i => E.wtSAW (E.emb i)) := hZ.comp_injective E.emb_inj
  have hnn : ∀ i, 0 ≤ E.wtSAW (E.emb i) := fun i => E.wtSAW_nn _
  
  have hsig : Summable
      (fun p : Σ v : ℕ, {i // E.scale i = v} => E.wtSAW (E.emb p.2.1)) := by
    have h := ((Equiv.sigmaFiberEquiv E.scale).summable_iff
      (f := fun i => E.wtSAW (E.emb i))).mpr htot
    refine h.congr (fun p => ?_)
    rw [Function.comp_apply, Equiv.sigmaFiberEquiv_apply]
  exact (summable_sigma_of_nonneg (fun p => hnn _) |>.mp hsig).2

end HexColumnEmb
end StatMech.Universality
