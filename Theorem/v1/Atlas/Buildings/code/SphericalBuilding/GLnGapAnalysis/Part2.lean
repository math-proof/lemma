/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/SphericalBuilding/GLnGapAnalysis.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnPanelExtension
import Def.v1.Atlas.Buildings.code.SphericalBuilding.GLnGapAnalysis


namespace GLnBuilding

variable (k : Type*) [Field k] (n : ℕ)


/-- Inserting two different elements at the same position yields different lists. -/
theorem insertIdx_ne_of_ne {α : Type*} {l : List α} {a b : α} {i : ℕ}
    (hne : a ≠ b) (hi : i ≤ l.length) :
    l.insertIdx i a ≠ l.insertIdx i b := by
  intro heq
  apply hne
  have hlen : i < (l.insertIdx i a).length := by
    rw [List.length_insertIdx]; split <;> omega
  have ha := List.getElem_insertIdx_self hlen
  have hlen' : i < (l.insertIdx i b).length := by
    rw [List.length_insertIdx]; split <;> omega
  have hb := List.getElem_insertIdx_self hlen'
  have : (l.insertIdx i a)[i]'hlen = (l.insertIdx i b)[i]'hlen' := by
    simp only [heq]
  rw [ha, hb] at this
  exact this


end GLnBuilding
