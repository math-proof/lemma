/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicSquareWiredPortGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredOneVisitInsertedPhase
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredTangentCode
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardAdaptiveClosure
import Theorem.StatisticalMechanics.Code.FrontierA.KacWardRectilinearPolygonBridge.Part2
import Def.StatisticalMechanics.Code.Universality.IsingFermionicSquareWiredPortGeometry.Part28


namespace StatMech.Universality

open StatMech StatMech.FK StatMech.Lattice StatMech.FrontierD

open scoped Affine

noncomputable section

theorem fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : (e, .south) ∈
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (e, .south) = fkIsingSquareWiredSourceDart n hn := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | bottom => simpa [fkIsingSquareWiredSourceDart] using hi.symm
  | west k | north k | top =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs

theorem fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
    (n : Nat) (hn : 0 < n)
    (e : FKIsingMedialVertex (fkSquareBoxPlanar n))
    (h : (e, .north) ∈
      Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)) :
    (e, .north) = fkIsingSquareWiredTerminalDart n hn ∨
      ∃ k : Fin (2 * n),
        (e, .north) = fkIsingSquareWiredBoundaryDart n hn (.north k) := by
  obtain ⟨i, hi⟩ := h
  cases i with
  | bottom | west k =>
      have hs := congrArg Prod.snd hi
      simp [fkIsingSquareWiredBoundaryEmbedding,
        fkIsingSquareWiredBoundaryDart,
        fkIsingSquareDirectionDart,
        fkIsingSquareEndpointForDirection,
        fkIsingSquareCornerSide] at hs
  | north k => exact Or.inr ⟨k, hi.symm⟩
  | top => exact Or.inl (by
      simpa [fkIsingSquareWiredTerminalDart] using hi.symm)

theorem fkIsingSquareWiredPortMacroStepWord_ne_nil
    (n : Nat) (hn : 0 < n)
    (omega : ConfigSpace (Sym2 (fkSquareBoxPlanar n).V))
    (d : FKIsingMedialDart (fkSquareBoxPlanar n))
    (hsource : d ≠ fkIsingSquareWiredSourceDart n hn)
    (hterminal : d ≠ fkIsingSquareWiredTerminalDart n hn) :
    fkIsingSquareWiredPortMacroStepWord n hn omega d ≠ [] := by
  rcases d with ⟨e, side⟩
  cases side with
  | west => simp [fkIsingSquareWiredPortMacroStepWord]
  | east => simp [fkIsingSquareWiredPortMacroStepWord]
  | south =>
      have hboundary : (e, .south) ∉
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) := by
        intro h
        exact hsource
          (fkIsingSquareWiredBoundaryEmbedding_south_eq_source_early n hn e h)
      have hword := fkIsingSquareWiredOrdinaryBondStepWord_ne_nil
        n hn (e, .south)
      simpa [fkIsingSquareWiredPortMacroStepWord] using hword
  | north =>
      by_cases hboundary : (e, .north) ∈
          Set.range (fkIsingSquareWiredBoundaryEmbedding n hn)
      · rcases
          fkIsingSquareWiredBoundaryEmbedding_north_eq_terminal_or_north_early
            n hn e hboundary with hterm | ⟨k, hk⟩
        · exact False.elim (hterminal hterm)
        · rw [hk]
          have he := congrArg Prod.fst hk
          simp only at he
          subst e
          have hrange : fkIsingSquareWiredBoundaryDart n hn (.north k) ∈
              Set.range (fkIsingSquareWiredBoundaryEmbedding n hn) :=
            ⟨.north k, rfl⟩
          simp [fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide] at hrange
          simp [fkIsingSquareWiredPortMacroStepWord,
            fkIsingSquareWiredBoundaryDart,
            fkIsingSquareDirectionDart,
            fkIsingSquareEndpointForDirection,
            fkIsingSquareCornerSide, hrange,
            fkIsingSquareWiredBulgeReverseStepWord]
      ·
        have hword := fkIsingSquareWiredOrdinaryBondStepWord_ne_nil
          n hn (e, .north)
        simpa [fkIsingSquareWiredPortMacroStepWord, hboundary] using hword

end
end StatMech.Universality
