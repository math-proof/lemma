/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWQOneMixedSquare.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part5
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Percolation.PcUpperViaFK.Part4
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Instance.StatisticalMechanics.Code.Universality.RSWQOneMixedSquare
open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.FK

open StatMech.RSW.Box

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem rq1_mixedSquareWiring_bottom_adj {n : ℕ} {x y : boxVerts 2 n}
    (hne : x ≠ y)
    (hx : (x : Site 2) 1 = -(n : ℤ)) (hy : (y : Site 2) 1 = -(n : ℤ)) :
    (rq1_mixedSquareWiring n).Adj x y :=
  ⟨hne, Or.inl ⟨hx, hy⟩⟩


theorem rq1_mixedSquareWiring_top_adj {n : ℕ} {x y : boxVerts 2 n}
    (hne : x ≠ y)
    (hx : (x : Site 2) 1 = (n : ℤ)) (hy : (y : Site 2) 1 = (n : ℤ)) :
    (rq1_mixedSquareWiring n).Adj x y :=
  ⟨hne, Or.inr ⟨hx, hy⟩⟩


theorem rq1_mixedSquareWiring_bottom_reachable {n : ℕ} {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ)) (hy : (y : Site 2) 1 = -(n : ℤ)) :
    (rq1_mixedSquareWiring n).Reachable x y := by
  by_cases hxy : x = y
  · subst y
    exact SimpleGraph.Reachable.refl x
  · exact (rq1_mixedSquareWiring_bottom_adj hxy hx hy).reachable


theorem rq1_mixedSquareWiring_top_reachable {n : ℕ} {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = (n : ℤ)) (hy : (y : Site 2) 1 = (n : ℤ)) :
    (rq1_mixedSquareWiring n).Reachable x y := by
  by_cases hxy : x = y
  · subst y
    exact SimpleGraph.Reachable.refl x
  · exact (rq1_mixedSquareWiring_top_adj hxy hx hy).reachable

theorem rq1_mixedSquareWiring_adj_preserves_bottom {n : ℕ} (hn : 0 < n)
    {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ))
    (hxy : (rq1_mixedSquareWiring n).Adj x y) :
    (y : Site 2) 1 = -(n : ℤ) := by
  rcases hxy.2 with hbottom | htop
  · exact hbottom.2
  · omega


theorem rq1_mixedSquareWiring_reachable_preserves_bottom {n : ℕ} (hn : 0 < n)
    {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ))
    (hxy : (rq1_mixedSquareWiring n).Reachable x y) :
    (y : Site 2) 1 = -(n : ℤ) := by
  have hwalk : ∀ {u v : boxVerts 2 n},
      (rq1_mixedSquareWiring n).Walk u v →
      (u : Site 2) 1 = -(n : ℤ) → (v : Site 2) 1 = -(n : ℤ) := by
    intro u v w hu
    induction w with
    | nil => exact hu
    | @cons a b c hab w ih =>
        exact ih (rq1_mixedSquareWiring_adj_preserves_bottom hn hu hab)
  exact hxy.elim fun w => hwalk w hx


theorem rq1_mixedSquareWiring_top_bottom_not_reachable {n : ℕ} (hn : 0 < n)
    {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ)) (hy : (y : Site 2) 1 = (n : ℤ)) :
    ¬ (rq1_mixedSquareWiring n).Reachable x y := by
  intro hxy
  have := rq1_mixedSquareWiring_reachable_preserves_bottom hn hx hxy
  omega


theorem rq1_mixedSquareWiring_top_bottom_not_joined {n : ℕ} (hn : 0 < n)
    {x y : boxVerts 2 n}
    (hx : (x : Site 2) 1 = -(n : ℤ)) (hy : (y : Site 2) 1 = (n : ℤ)) :
    ¬ (rq1_mixedSquareWiring n).Adj x y := by
  intro hxy
  exact rq1_mixedSquareWiring_top_bottom_not_reachable hn hx hy hxy.reachable


theorem rq1_mixedSquare_crossing_lower_bound (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / (1 + 1 ^ 2) ≤
      ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)),
        (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta *
          bcProb (boxGraph 2 n) (rq1_mixedSquareWiring n)
            ((1 : ℝ) / 2) 1 eta := by
  norm_num
  exact rq1_bcMixedSquare_crossing_half n hn (rq1_mixedSquareWiring n)


theorem rq1_wiredSquare_crossing_half (n : ℕ) (hn : 0 < n) :
    (1 : ℝ) / 2 ≤
      ∑ eta : ConfigSpace (Sym2 (boxVerts 2 n)),
        (rq1_finiteMixedSquareEvent n).indicator (fun _ => (1 : ℝ)) eta *
          wiredFkProb (boxGraph 2 n) (boxBoundary 2 n)
            ((1 : ℝ) / 2) 1 eta := by
  simpa only [bcProb_clique_eq_wiredFkProb] using
    rq1_bcMixedSquare_crossing_half n hn
      (StatMech.Lattice.boundaryCliqueGraph (boxBoundary 2 n))


end Universality
end StatMech
