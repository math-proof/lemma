/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWindowRealization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalAverageAnchor
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicCaratheodoryHolderAnchor.Part3
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWindowRealization


namespace StatMech.Universality

open Finset

noncomputable section

theorem fkIsingSquareRadialPatchWindowCarrier_injective
    (n m baseI baseJ R : Nat) (hm : m ≤ n)
    (hfitI : baseI + R + 1 < m) (hfitJ : baseJ + R + 1 < m) :
    Function.Injective
      (fkIsingSquareRadialPatchWindowCarrier
        n m baseI baseJ R hm hfitI hfitJ) := by
  intro p q hpq
  have hedge :
      fkIsingSquareRadialPatchEdge n m hm
          ⟨baseI + p.1.1, by have := p.1.2; omega⟩
          ⟨baseJ + p.2.1, by have := p.2.2; omega⟩ =
        fkIsingSquareRadialPatchEdge n m hm
          ⟨baseI + q.1.1, by have := q.1.2; omega⟩
          ⟨baseJ + q.2.1, by have := q.2.2; omega⟩ := by
    simpa [fkIsingSquareRadialPatchWindowCarrier] using hpq
  have hcell := fkIsingSquareRadialPatchEdge_injective n m hm
    (a₁ :=
      (⟨baseI + p.1.1, by have := p.1.2; omega⟩,
        ⟨baseJ + p.2.1, by have := p.2.2; omega⟩))
    (a₂ :=
      (⟨baseI + q.1.1, by have := q.1.2; omega⟩,
        ⟨baseJ + q.2.1, by have := q.2.2; omega⟩)) hedge
  apply Prod.ext <;> apply Fin.ext
  · have := congrArg (fun x : Fin m × Fin m ↦ x.1.1) hcell
    change baseI + p.1.1 = baseI + q.1.1 at this
    omega
  · have := congrArg (fun x : Fin m × Fin m ↦ x.2.1) hcell
    change baseJ + p.2.1 = baseJ + q.2.1 at this
    omega


end
end StatMech.Universality
