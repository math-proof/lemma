import Mathlib
import sympy.Basic
import sympy.analysis.MeasureTheory.Section_1_2_0
open BoundedInterval


/--
[tsum_volume_finset_eq](https://github.com/teorth/analysis/blob/main/Analysis/MeasureTheory/Section_1_2_0.lean)
-/
@[path]
private lemma main
  {d : ℕ}
  {S : Finset (Box d)}
-- given
  (hd : 0 < d) :
-- imply
  let S_list := S.toList
  let zero_box : Box d := ⟨fun i => if i.val = 0 then ∅ else BoundedInterval.Icc 0 0⟩
  let S_seq : ℕ → Box d := fun n =>
    if h : n < S_list.length then S_list.get ⟨n, h⟩ else zero_box
  ∑' n, (S_seq n).volume.toEReal = (∑ B ∈ S, |B|ᵥ).toEReal :=
-- proof
  tsum_volume_finset_eq hd S


-- created on 2026-10-22
