/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Def.StatisticalMechanics.Code.FK.TwoPointInfinite.Part4
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators NNReal Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {E : Type*} [Countable E]


theorem freeIvTwoPoint_pos (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d N}
    (h : (boxGraph d N).Reachable x y) :
    0 < freeIvTwoPoint d N hp hp1 hq x y :=
  ivTwoPointSup_pos _ _ (freeFiniteMeasure_apply_boxConnEvent_pos d N hp hp1 hq h)


theorem freeIvTwoPoint_self_pos (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x : boxVerts d N) :
    0 < freeIvTwoPoint d N hp hp1 hq x x :=
  freeIvTwoPoint_pos d N hp hp1 hq (SimpleGraph.Reachable.refl x)


theorem wiredIvTwoPoint_pos_of_uniform (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d N} {c : NNReal} (hc : 0 < c)
    (hbound : ∀ n, c ≤ (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) :
    0 < wiredIvTwoPoint d N hp hp1 hq x y :=
  ivTwoPointInf_pos_of_uniform _ _ hc hbound


theorem freeIvTwoPoint_isLimit (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hchain : ∀ n, (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (freeFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (x y : boxVerts d N) :
    Tendsto (fun n => (freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) atTop
      (𝓝 (freeIvTwoPoint d N hp hp1 hq x y)) :=
  ivTwoPointSup_isLimit _ hchain (isClopen_boxConnEvent d N x y) (isIncreasing_boxConnEvent d N x y)


theorem wiredIvTwoPoint_isLimit (d N : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (hchain : ∀ n, (wiredFiniteMeasure d (n + 1) hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d))))
        ≼ (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))))
    (x y : boxVerts d N) :
    Tendsto (fun n => (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d N x y)) atTop
      (𝓝 (wiredIvTwoPoint d N hp hp1 hq x y)) :=
  ivTwoPointInf_isLimit _ hchain (isClopen_boxConnEvent d N x y) (isIncreasing_boxConnEvent d N x y)

end FK
end StatMech
