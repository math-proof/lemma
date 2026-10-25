/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc6raysetdef.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc3_core.Part3
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Def.StatisticalMechanics.Code.Walls.bc6raysetdef
open Set
open StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation StatMech.Percolation.DisjointPaths


namespace StatMech

namespace Walls

variable {d : ℕ}


lemma bc6_mem_rayInterior {a : Fin d} {R : ℕ} {x : Site d} :
    x ∈ bc6_rayInterior a R ↔ ∃ p : ℕ, (1 ≤ p ∧ p ≤ R) ∧ x = hrHD_rayPt a (p : ℤ) :=
  Iff.rfl


lemma bc6_rayPt_mem_rayInterior {a : Fin d} {R p : ℕ} (h1 : 1 ≤ p) (h2 : p ≤ R) :
    hrHD_rayPt a (p : ℤ) ∈ bc6_rayInterior a R :=
  ⟨p, ⟨h1, h2⟩, rfl⟩


lemma bc6_mouth_mem_rayInterior {a : Fin d} {R : ℕ} (hR : 1 ≤ R) :
    (hrHD_rayPt a 1 : Site d) ∈ bc6_rayInterior a R := by
  have h : hrHD_rayPt a ((1 : ℕ) : ℤ) = hrHD_rayPt a 1 := by norm_num
  rw [← h]
  exact bc6_rayPt_mem_rayInterior le_rfl hR


lemma bc6_origin_notMem_rayInterior {a : Fin d} {R : ℕ} :
    (0 : Site d) ∉ bc6_rayInterior a R := by
  rintro ⟨p, ⟨hp1, _⟩, hp0⟩
  have : hrHD_rayPt a (p : ℤ) = (0 : Site d) := hp0.symm
  rw [hrHD_rayPt_eq_zero_iff] at this
  omega


end Walls
end StatMech
