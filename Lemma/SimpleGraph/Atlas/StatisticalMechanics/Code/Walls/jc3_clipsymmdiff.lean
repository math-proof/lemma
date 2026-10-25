import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc3_clipsymmdiff
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc3_mem_clip_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_mem_clip_iff_eq
  {K : Set α}
  {r c : α} :
-- imply
  c ∈ K \ {r} ↔ (c ∈ K ∧ c ≠ r) := by
-- proof
  apply StatMech.Walls.jc3_mem_clip_iff K r c

/--
[jc3_clip_eq_iff_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_clip_eq_iff_ne_eq
  {K : Set α}
  {r c : α}
-- given
  (hne : c ≠ r) :
-- imply
  c ∈ K ↔ c ∈ K \ {r} := by
-- proof
  apply StatMech.Walls.jc3_clip_eq_iff_ne K r c hne

/--
[jc3_ear_not_mem_clip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_ear_not_mem_clip_eq
  {K : Set α}
  {r : α} :
-- imply
  r ∉ K \ {r} := by
-- proof
  apply StatMech.Walls.jc3_ear_not_mem_clip K r

/--
[jc3_clip_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_clip_symmDiff_eq
  {K : Set α}
  {r : α}
-- given
  (hr : r ∈ K) :
-- imply
  K ∆ (K \ {r}) = {r} := by
-- proof
  apply StatMech.Walls.jc3_clip_symmDiff K r hr

/--
[jc3_clip_ssubset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_clip_ssubset_eq
  {K : Set α}
  {r : α}
-- given
  (hr : r ∈ K) :
-- imply
  K \ {r} ⊂ K := by
-- proof
  apply StatMech.Walls.jc3_clip_ssubset K r hr

/--
[jc3_clip_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_clip_finite_eq
  {K : Set α}
  {r : α}
-- given
  (hK : K.Finite) :
-- imply
  (K \ {r}).Finite := by
-- proof
  apply StatMech.Walls.jc3_clip_finite K r hK

/--
[jc3_clip_nonempty_of_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_clip_nonempty_of_two_eq
  {K : Set α}
  {r s : α}
-- given
  (hs : s ∈ K)
  (hsr : s ≠ r) :
-- imply
  (K \ {r}).Nonempty := by
-- proof
  apply StatMech.Walls.jc3_clip_nonempty_of_two K r s hs hsr

/--
[jc3_ear_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_ear_mem_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len) :
-- imply
  jc2_rightEnd c len ∈ K := by
-- proof
  apply StatMech.Walls.jc3_ear_mem K c len hrun

/--
[jc3_clip_symmDiff_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_clip_symmDiff_ear_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
-- given
  (hrun : jc_IsTopRowRun K c len) :
-- imply
  K ∆ (K \ {jc2_rightEnd c len}) = {jc2_rightEnd c len} := by
-- proof
  apply StatMech.Walls.jc3_clip_symmDiff_ear K c len hrun

/--
[jc3_probe_mem_iff_ear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_probe_mem_iff_ear_eq
  {K : Set (Site 2)}
  {c : Site 2}
  {len : ℤ}
  {s : Site 2}
-- given
  (hne : s ≠ jc2_rightEnd c len) :
-- imply
  s ∈ K ↔ s ∈ K \ {jc2_rightEnd c len} := by
-- proof
  apply StatMech.Walls.jc3_probe_mem_iff_ear K c len s hne

/--
[jc3_clip_agree_of_notProbed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_clip_agree_of_notProbed_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (h : bpc_NotProbed r e) :
-- imply
  (e.head + (-rot90Fun e.dir) ∈ K ↔ e.head + (-rot90Fun e.dir) ∈ K \ {r}) ∧ (e.tail + (-rot90Fun e.dir) ∈ K ↔ e.tail + (-rot90Fun e.dir) ∈ K \ {r}) := by
-- proof
  apply StatMech.Walls.jc3_clip_agree_of_notProbed K r e h

/--
[jc3_notProbed_iff_clip_agree_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_notProbed_iff_clip_agree_of_mem_eq
  {K : Set (Site 2)}
  {r : Site 2}
  {e : Dart}
-- given
  (hr : r ∈ K) :
-- imply
  bpc_NotProbed r e ↔ ((e.head + (-rot90Fun e.dir) ∈ K ↔ e.head + (-rot90Fun e.dir) ∈ K \ {r}) ∧ (e.tail + (-rot90Fun e.dir) ∈ K ↔ e.tail + (-rot90Fun e.dir) ∈ K \ {r})) := by
-- proof
  apply StatMech.Walls.jc3_notProbed_iff_clip_agree_of_mem K r e hr

/--
[jc3_domino_clip_symmDiff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_domino_clip_symmDiff_eq :
-- imply
  domino ∆ (domino \ {(![1, 0] : Site 2)}) = {(![1, 0] : Site 2)} := by
-- proof
  apply StatMech.Walls.jc3_domino_clip_symmDiff

/--
[jc3_unitCell_clip_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc3_clipsymmdiff.lean)
-/
@[path]
private lemma jc3_unitCell_clip_self_eq :
-- imply
  unitCell \ {(![0, 0] : Site 2)} = (∅ : Set (Site 2)) := by
-- proof
  apply StatMech.Walls.jc3_unitCell_clip_self


-- created on 2026-10-23
