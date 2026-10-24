import Mathlib
import sympy.Basic
import sympy.atlas.Data.Set.Triplewise
open Set


namespace Set

/--
[Triplewise.eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
protected lemma Triplewise.eq
  {r : α → α → α → Prop}
  {s t : Set α}
  {x y z : α}
-- given
  (hs : s.Triplewise r)
  (hx : x ∈ s)
  (hy : y ∈ s)
  (hz : z ∈ s)
  (h : ¬r x y z) :
-- imply
  x = y ∨ y = z ∨ x = z := by
-- proof
  have := (h <| hs hx hy hz · · ·)
  tauto

end Set

namespace Set

/--
[Triplewise.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
lemma Triplewise.mono
  {r : α → α → α → Prop}
  {s t : Set α}
-- given
  (h : t ⊆ s)
  (hs : s.Triplewise r) :
-- imply
  t.Triplewise r :=
-- proof
  fun _ hx _ hy _ hz hxy hyz hxz ↦ hs (h hx) (h hy) (h hz) hxy hyz hxz

end Set

namespace Set

/--
[Triplewise_univ_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
lemma Triplewise_univ_iff
  {r : α → α → α → Prop} :
-- imply
  Triplewise r ↔ Triplewise r := by
-- proof
  simp [Set.Triplewise, Triplewise]

end Set

namespace Set

/--
[triplewise_of_encard_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
lemma triplewise_of_encard_lt
  {s t : Set α}
-- given
  (r : α → α → α → Prop)
  (h : s.encard < 3) :
-- imply
  s.Triplewise r := by
-- proof
  unfold Set.Triplewise
  contrapose! h
  obtain ⟨x, hx, y, hy, z, hz, hxy, hyz, hxz, _⟩ := h
  trans encard {x, y, z}
  · simp [Set.encard_insert_of_notMem, *]
    norm_num
  · exact encard_le_encard_of_injOn (by simp [MapsTo, hx, hy, hz]) (injOn_id _)

end Set

namespace Set

/--
[triplewise_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
lemma triplewise_empty
-- given
  (r : α → α → α → Prop) :
-- imply
  Triplewise ∅ r :=
-- proof
  (notMem_empty · · |>.elim)

end Set

namespace Set

/--
[triplewise_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
lemma triplewise_singleton
  {x y z : α}
-- given
  (r : α → α → α → Prop) :
-- imply
  Triplewise {x} r := by
-- proof
  apply triplewise_of_encard_lt
  simp

end Set

namespace Set

/--
[triplewise_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
lemma triplewise_pair
  {x y z : α}
-- given
  (r : α → α → α → Prop) :
-- imply
  Triplewise {x, y} r := by
-- proof
  apply triplewise_of_encard_lt
  apply (encard_insert_le {y} x).trans_lt
  simp
  norm_num

end Set

namespace Set

/--
[triplewise_insert](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
lemma triplewise_insert
  {r : α → α → α → Prop}
  {s t : Set α}
  {x y z : α} :
-- imply
  (insert x s).Triplewise r ↔ s.Triplewise r ∧
    ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → r x y z ∧ r y x z ∧ r y z x := by
-- proof
  refine ⟨fun hxs ↦ ?_, fun ⟨hs, hxs⟩ ↦ ?_⟩
  · refine ⟨hxs.mono (subset_insert x s), fun y hy z hz hxy hxz hyz ↦ ⟨?_, ?_, ?_⟩⟩
    · exact hxs (mem_insert x s) (mem_insert_of_mem x hy) (mem_insert_of_mem x hz) hxy hyz hxz
    · exact hxs (mem_insert_of_mem x hy) (mem_insert x s) (mem_insert_of_mem x hz) hxy.symm hxz hyz
    · exact hxs (mem_insert_of_mem x hy) (mem_insert_of_mem x hz)
      (mem_insert x s) hyz hxz.symm hxy.symm
  · intro w hw y hy z hz hwy hyz hwz
    rw [mem_insert_iff] at hw hy hz
    obtain rfl | hw := hw
    · refine (hxs y ?_ z ?_ hwy hwz hyz).1
      · simpa [hwy.symm] using hy
      · simpa [hwz.symm] using hz
    obtain rfl | hy := hy
    · exact (hxs w hw z (by simpa [hyz.symm] using hz) hwy.symm hyz hwz).2.1
    obtain rfl | hz := hz
    · exact (hxs w hw y hy hwz.symm hyz.symm hwy).2.2
    exact hs hw hy hz hwy hyz hwz

end Set

namespace Set

/--
[triplewise_insert_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
lemma triplewise_insert_of_not_mem
  {r : α → α → α → Prop}
  {s t : Set α}
  {x y z : α}
-- given
  (hx : x ∉ s) :
-- imply
  (insert x s).Triplewise r ↔ s.Triplewise r ∧
    ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r x y z ∧ r y x z ∧ r y z x := by
-- proof
  refine Set.triplewise_insert.trans <| and_congr_right' <| forall₄_congr ?_
  intro y hy z hz
  simp [(ne_of_mem_of_not_mem hy hx).symm, (ne_of_mem_of_not_mem hz hx).symm]

end Set

namespace Set

/--
[Triplewise.insert](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
protected lemma Triplewise.insert
  {r : α → α → α → Prop}
  {s t : Set α}
  {x y z : α}
-- given
  (hs : s.Triplewise r)
  (h : ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → r x y z ∧ r y x z ∧ r y z x) :
-- imply
  (insert x s).Triplewise r :=
-- proof
  Set.triplewise_insert.mpr ⟨hs, h⟩

end Set

namespace Set

/--
[Triplewise.insert_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
protected lemma Triplewise.insert_of_not_mem
  {r : α → α → α → Prop}
  {s t : Set α}
  {x y z : α}
-- given
  (hx : x ∉ s)
  (hs : s.Triplewise r)
  (h : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r x y z ∧ r y x z ∧ r y z x) :
-- imply
  (insert x s).Triplewise r :=
-- proof
  (Set.triplewise_insert_of_not_mem hx).mpr ⟨hs, h⟩

end Set

namespace Set

/--
[triplewise_set_pred_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
lemma triplewise_set_pred_iff
  {S : Set α}
  {P : Set α → Prop} :
-- imply
  S.Triplewise (P {·, ·, ·}) ↔ ∀ T ⊆ S, T.ncard = 3 → P T := by
-- proof
  constructor
  · intro h T hT T_ncard
    obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := ncard_eq_three.mp T_ncard
    simp_rw [insert_subset_iff, singleton_subset_iff] at hT
    exact h hT.1 hT.2.1 hT.2.2 hxy hyz hxz
  · intro h x hx y hy z hz hxy hyz hxz
    refine h _ ?_ (ncard_eq_three.mpr ⟨x, y, z, hxy, hxz, hyz, rfl⟩)
    simp [insert_subset_iff, hx, hy, hz]

end Set


-- created on 2026-10-20
-- updated on 2026-10-23
