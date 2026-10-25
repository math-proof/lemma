/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/LongRectangleTorusPushforward.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusCover.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Def.StatisticalMechanics.Code.BeffaraDC.LongRectangleTorusPushforward.Part4
open MeasureTheory Set
open scoped ENNReal NNReal


namespace StatMech.BeffaraDC

open StatMech.Lattice

open StatMech.Onsager

open StatMech.Universality


@[simp] theorem torusSiteTranslateEquiv_apply
    (L : ℕ) (t : Site 2) (z : ZMod L × ZMod L) :
    torusSiteTranslateEquiv L t z =
      (z.1 + (t 0 : ZMod L), z.2 + (t 1 : ZMod L)) :=
  rfl


theorem torusReduceSite_add (L : ℕ) (z t : Site 2) :
    torusReduceSite L (z + t) = torusSiteTranslateEquiv L t (torusReduceSite L z) := by
  apply Prod.ext <;> simp [torusReduceSite, torusSiteTranslateEquiv]


theorem onsTorusGraph_adj_translate (L : ℕ) [Fact (2 < L)]
    (t : Site 2) (x y : ZMod L × ZMod L) :
    (onsTorusGraph L).Adj (torusSiteTranslateEquiv L t x)
        (torusSiteTranslateEquiv L t y) ↔
      (onsTorusGraph L).Adj x y := by
  change onsTorusAdj L
      (x.1 + (t 0 : ZMod L), x.2 + (t 1 : ZMod L))
      (y.1 + (t 0 : ZMod L), y.2 + (t 1 : ZMod L)) ↔
    onsTorusAdj L x y
  unfold onsTorusAdj
  constructor
  · rintro (⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩)
    · exact Or.inl ⟨by linear_combination h0, Or.inl (by linear_combination h1)⟩
    · exact Or.inl ⟨by linear_combination h0, Or.inr (by linear_combination h1)⟩
    · exact Or.inr ⟨by linear_combination h1, Or.inl (by linear_combination h0)⟩
    · exact Or.inr ⟨by linear_combination h1, Or.inr (by linear_combination h0)⟩
  · rintro (⟨h0, h1 | h1⟩ | ⟨h1, h0 | h0⟩)
    · exact Or.inl ⟨by linear_combination h0, Or.inl (by linear_combination h1)⟩
    · exact Or.inl ⟨by linear_combination h0, Or.inr (by linear_combination h1)⟩
    · exact Or.inr ⟨by linear_combination h1, Or.inl (by linear_combination h0)⟩
    · exact Or.inr ⟨by linear_combination h1, Or.inr (by linear_combination h0)⟩


theorem torusSiteTranslate_mem_edgeFinset_iff
    (L : ℕ) [Fact (2 < L)] (t : Site 2)
    (e : Sym2 (ZMod L × ZMod L)) :
    Sym2.map (torusSiteTranslateEquiv L t) e ∈
        (onsTorusGraph L).edgeFinset ↔
      e ∈ (onsTorusGraph L).edgeFinset := by
  induction e using Sym2.ind with
  | _ x y =>
      simp only [Sym2.map_mk, SimpleGraph.mem_edgeFinset,
        SimpleGraph.mem_edgeSet]
      exact onsTorusGraph_adj_translate L t x y


end StatMech.BeffaraDC
