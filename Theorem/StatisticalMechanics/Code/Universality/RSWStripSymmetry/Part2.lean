/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWStripSymmetry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Def.StatisticalMechanics.Code.Universality.RSWStripSymmetry.Part2
open Set SimpleGraph MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal


namespace StatMech

namespace Universality

open StatMech.Lattice


theorem rss_mem_faceStrip_reflect (n : ℤ) (x : Site 2) :
    x ∈ rss_faceStrip n ↔ rss_stripReflect n x ∈ rss_faceStrip n := by
  simp only [rss_faceStrip, Set.mem_setOf_eq, rss_stripReflect_one]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> omega


theorem rss_mem_bottom_reflect_iff_top (n : ℤ) (x : Site 2) :
    x ∈ rss_bottomFaceLine n ↔ rss_stripReflect n x ∈ rss_topFaceLine n := by
  simp [rss_bottomFaceLine, rss_topFaceLine]
  omega


theorem rss_mem_top_reflect_iff_bottom (n : ℤ) (x : Site 2) :
    x ∈ rss_topFaceLine n ↔ rss_stripReflect n x ∈ rss_bottomFaceLine n := by
  simp [rss_bottomFaceLine, rss_topFaceLine]
  omega


end Universality
end StatMech
