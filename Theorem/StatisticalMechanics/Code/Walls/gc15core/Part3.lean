/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc15core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.MultiReplica.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.gc8Z0pos
import Def.StatisticalMechanics.Code.Walls.gc15core.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


variable (S : SimpleGraph V) [DecidableRel S.Adj]


theorem gc15_Z0_pos (β h : ℝ) : 0 < gc15_Z0 G β h := gc8_Z0_pos_ghost G β h


theorem gc15_u3_ghost_expectationJ (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    eg_ursell3 G β h o x y
      = expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({o} : Finset V).map someEmb))
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (({x, y} : Finset V).map someEmb)
        - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, x} : Finset V).map someEmb)
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({y} : Finset V).map someEmb))
        - expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, y} : Finset V).map someEmb)
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({x} : Finset V).map someEmb))
        + 2 * (expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({o} : Finset V).map someEmb))
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({x} : Finset V).map someEmb))
            * expectationJ (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({y} : Finset V).map someEmb))) := by
  unfold eg_ursell3
  rw [← gc10_moment_oxyg G β h o x y hox hoy hxy,
      ← gc10_moment_ghostSingle G β h o, ← gc10_moment_pair G β h x y hxy,
      ← gc10_moment_pair G β h o x hox, ← gc10_moment_ghostSingle G β h y,
      ← gc10_moment_pair G β h o y hoy, ← gc10_moment_ghostSingle G β h x]
  ring


theorem gc15_u3_currentSum_poly (β h : ℝ) (o x y : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (gc15_Z0 G β h) ^ 3 * eg_ursell3 G β h o x y
      = (gc15_Z0 G β h) ^ 2 * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
            (insert (none : Option V) (({o, x, y} : Finset V).map someEmb))
        - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (insert (none : Option V) (({o} : Finset V).map someEmb))
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (({x, y} : Finset V).map someEmb)
        - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, x} : Finset V).map someEmb)
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({y} : Finset V).map someEmb))
        - (gc15_Z0 G β h) * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
              (({o, y} : Finset V).map someEmb)
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({x} : Finset V).map someEmb))
        + 2 * (currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({o} : Finset V).map someEmb))
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({x} : Finset V).map someEmb))
            * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
                (insert (none : Option V) (({y} : Finset V).map someEmb))) := by
  rw [gc15_u3_ghost_expectationJ G β h o x y hox hoy hxy,
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o} : Finset V).map someEmb)),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1)) (({x, y} : Finset V).map someEmb),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1)) (({o, x} : Finset V).map someEmb),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({y} : Finset V).map someEmb)),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1)) (({o, y} : Finset V).map someEmb),
    gc8_eq15_insertion_ghost G β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({x} : Finset V).map someEmb))]
  unfold gc15_Z0
  ring


theorem gc15_gsingle (a : V) :
    insert (none : Option V) (({a} : Finset V).map someEmb)
      = ({some a, none} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_singleton, someEmb,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro (rfl | ⟨b, rfl, rfl⟩) <;> tauto
  · rintro (rfl | rfl) <;> tauto


theorem gc15_gpair (a b : V) :
    (({a, b} : Finset V).map someEmb) = ({some a, some b} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_map, Finset.mem_insert, Finset.mem_singleton, someEmb,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨c, hc, rfl⟩; rcases hc with rfl | rfl <;> tauto
  · rintro (rfl | rfl) <;> [exact ⟨a, by tauto, rfl⟩; exact ⟨b, by tauto, rfl⟩]


theorem gc15_gquad (o x y : V) :
    insert (none : Option V) (({o, x, y} : Finset V).map someEmb)
      = ({some o, some x, some y, none} : Finset (Option V)) := by
  ext z; simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_singleton, someEmb,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro (rfl | ⟨b, hb, rfl⟩) <;> [tauto; (rcases hb with rfl | rfl | rfl <;> tauto)]
  · rintro (rfl | rfl | rfl | rfl) <;>
      first | (left; rfl) | (right; exact ⟨_, by tauto, rfl⟩)


theorem gc15_marks_distinct {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    (some o ≠ some x) ∧ (some o ≠ some y) ∧ (some o ≠ (none : Option V))
      ∧ (some x ≠ some y) ∧ (some x ≠ (none : Option V)) ∧ (some y ≠ (none : Option V)) :=
  ⟨by simp [hox], by simp [hoy], by simp, by simp [hxy], by simp, by simp⟩


end StatMech.Walls
