/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gh9switchrearrange.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gh8weightedassembly.Part2
import Theorem.StatisticalMechanics.Code.Walls.gh5currentrep.Part3
import Theorem.StatisticalMechanics.Code.Walls.ghggrahamclose
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.GhcEqGap

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable {W : Type*} [DecidableEq W] [Fintype W]

variable {V : Type*} [Fintype V] [DecidableEq V]


theorem gh9_pcount_regroup_real (ends : ι → Sym2 W) (m : Finset ι) (V₁ V₂ : Finset W) (u : W) :
    (gc85b_pcount ends m V₁ V₂ : ℝ)
      = ∑ A ∈ m.powerset, (gh4_compMass ends m V₁ V₂ u A : ℝ) := by
  rw [gh4_compMass_partition ends m V₁ V₂ u]
  push_cast
  rfl


theorem gh9_lemma2_reroute (ends : ι → Sym2 W) (m : Finset ι) (A B : Finset W)
    {u v : W} (huv : u ≠ v) (P : Finset ι) (hPm : P ⊆ m) (hPsrc : sources ends P = {u, v}) :
    #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B ∆ {u, v}))
      = #((m.powerset ×ˢ m.powerset).filter
        (fun KK => Disjoint KK.1 KK.2 ∧ Disjoint KK.1 P
          ∧ sources ends KK.1 = A ∧ sources ends KK.2 = B)) :=
  gc85b_pcount_reroute_eq ends m A B huv P hPm hPsrc


theorem gh9_flux_dichotomy (ends : ι → Sym2 W) (R : Finset ι)
    (hnd : ∀ i ∈ R, ¬ (ends i).IsDiag) {o x y g : W}
    (hsrc : sources ends R = ({o, x, y, g} : Finset W))
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) :
    Odd (#((({x, y, g} : Finset W)).filter (fun w => connK ends R o w))) :=
  ghg_flux_dichotomy ends R hnd hsrc hox hoy hog


theorem gh9_ursell3_currentSum_poly (G : SimpleGraph V) [DecidableRel G.Adj] (β h : ℝ)
    (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
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
                (insert (none : Option V) (({y} : Finset V).map someEmb))) :=
  gc15_u3_currentSum_poly G β h o x y hox hoy hxy


end StatMech.Walls
