/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/MengerSplice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.SimpleGraph.Paths


namespace StatMech.Combinatorics

open SimpleGraph SimpleGraph.Walk

variable {V : Type*} {G : SimpleGraph V}


lemma mgs_start_not_mem_tail {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have hnd := hp.support_nodup
  rw [← cons_tail_support] at hnd
  exact (List.nodup_cons.mp hnd).1


lemma mgs_append_isPath {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath)
    (hmeet : ∀ x, x ∈ p.support → x ∈ q.support → x = v) :
    (p.append q).IsPath := by
  rw [isPath_def, support_append]
  refine List.Nodup.append hp.support_nodup ((List.tail_sublist _).nodup hq.support_nodup) ?_
  rw [List.disjoint_left]
  intro x hxp hxqt
  have hxq : x ∈ q.support := List.tail_subset _ hxqt
  have hxv : x = v := hmeet x hxp hxq
  subst hxv
  exact (mgs_start_not_mem_tail hq) hxqt


end StatMech.Combinatorics
