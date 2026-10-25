/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredCompletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareBox.Part39
import Mathlib.Logic.Equiv.Fintype
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredCompletion.Part4


namespace StatMech.Universality

open Finset SimpleGraph

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

noncomputable section

theorem fkIsingSquareDart_key_injective (n : Nat) :
    Function.Injective (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
      (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
        d.2)) := by
  intro d f h
  rcases Prod.mk.inj h with ⟨he, hrest⟩
  rcases Prod.mk.inj hrest with ⟨hdr, hs⟩
  apply Prod.ext
  · calc
      d.1 = fkIsingSquareDirectionEdge n (fkIsingSquareDartEndpoint n d)
          (fkIsingSquareDartDirection n d)
          (fkIsingSquareDartDirection_available n d) :=
        (fkIsingSquareDirectionEdge_reconstruct n d).symm
      _ = fkIsingSquareDirectionEdge n (fkIsingSquareDartEndpoint n f)
          (fkIsingSquareDartDirection n f)
          (fkIsingSquareDartDirection_available n f) := by congr
      _ = f.1 := fkIsingSquareDirectionEdge_reconstruct n f
  · exact hs

theorem fkIsingSquareWiredBoundaryDart_injective (n : Nat) (hn : 0 < n) :
    Function.Injective (fkIsingSquareWiredBoundaryDart n hn) := by
  intro i j h
  have hkey := congrArg (fun d : FKIsingMedialDart (fkSquareBoxPlanar n) =>
      (fkIsingSquareDartEndpoint n d, fkIsingSquareDartDirection n d,
        d.2)) h
  cases i <;> cases j <;>
    simp [fkIsingSquareWiredBoundaryDart, fkIsingSquareMarkedA,
      fkIsingSquareMarkedB, fkIsingSquareLeftVerticalLower,
      fkIsingSquareLeftVerticalUpper] at hkey ⊢
  all_goals try
    have hv := congrArg (fun x : (fkSquareBoxPlanar n).V => x.1 1) hkey.1
    simp at hv
    omega

end
end StatMech.Universality
