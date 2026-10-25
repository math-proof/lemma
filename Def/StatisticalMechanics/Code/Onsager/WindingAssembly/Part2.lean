/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/WindingAssembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Onsager.GroundUpWinding.Part4
import Theorem.StatisticalMechanics.Code.Onsager.SplitConstruction
import Theorem.StatisticalMechanics.Code.Onsager.PolygonWalk.Part3
import Theorem.StatisticalMechanics.Code.Onsager.WindingAssembly


namespace StatMech.Onsager.WindingAssembly

open StatMech.Onsager.SplitConstruction


def concretePolyData
    (hbase : ∀ V : List Pt, simplePred V → rcCount V = 0 → ccCount V = 4)
    (hchord : ∀ V : List Pt, simplePred V → 0 < rcCount V →
        ∃ a b : ℕ, a + 1 < b ∧ b < V.length ∧ (0 < a ∨ b + 1 < V.length) ∧
          isAxisAligned V[a]! V[b]! ∧
          ccCount (arc V a b) + ccCount (coarc V a b) = ccCount V + 3 ∧
          rcCount (arc V a b) + rcCount (coarc V a b) = rcCount V - 1) :
    StatMech.Onsager.GroundUp.RectPolygonData where
  Poly := List Pt
  size := List.length
  cc := ccCount
  rc := rcCount
  simple := simplePred
  hcc := fun P => ccCount_nonneg P
  hrc := fun P => rcCount_nonneg P
  base := hbase
  chord := by
    intro V hV hr
    obtain ⟨a, b, hab, hb, hstrict, hchd, hcceq, hrceq⟩ := hchord V hV hr
    have ha : a < V.length := by omega
    rw [getElem!_eq_getElem V a ha, getElem!_eq_getElem V b hb] at hchd
    obtain ⟨hs1, hs2, hlt1, hlt2⟩ :=
      structural_chord V a b hV.1 hV.2.1 hV.2.2 ha hb hab hstrict hchd
    exact ⟨arc V a b, coarc V a b, hs1, hs2, hlt1, hlt2, hcceq, hrceq⟩


end StatMech.Onsager.WindingAssembly
