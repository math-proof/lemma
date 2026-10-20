import Mathlib
import sympy.Basic
import sympy.atlas.Data.Set.Triplewise
open Set


/--
[Triplewise.eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma Triplewise_eq_eq
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
  apply Set.Triplewise.eq hs hx hy hz h

/--
[Triplewise.mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma Triplewise_mono_eq
  {r : α → α → α → Prop}
  {s t : Set α}
-- given
  (h : t ⊆ s)
  (hs : s.Triplewise r) :
-- imply
  t.Triplewise r := by
-- proof
  apply Set.Triplewise.mono h hs

/--
[Triplewise_univ_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma Triplewise_univ_iff_eq
  {r : α → α → α → Prop} :
-- imply
  Triplewise r ↔ Triplewise r := by
-- proof
  apply Set.Triplewise_univ_iff

/--
[triplewise_of_encard_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma triplewise_of_encard_lt_eq
  {s t : Set α}
-- given
  (r : α → α → α → Prop)
  (h : s.encard < 3) :
-- imply
  s.Triplewise r := by
-- proof
  apply Set.triplewise_of_encard_lt r h

/--
[triplewise_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma triplewise_empty_eq
-- given
  (r : α → α → α → Prop) :
-- imply
  Triplewise ∅ r := by
-- proof
  apply Set.triplewise_empty r

/--
[triplewise_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma triplewise_singleton_eq
  {x y z : α}
-- given
  (r : α → α → α → Prop) :
-- imply
  Triplewise {x} r := by
-- proof
  apply Set.triplewise_singleton r

/--
[triplewise_pair](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma triplewise_pair_eq
  {x y z : α}
-- given
  (r : α → α → α → Prop) :
-- imply
  Triplewise {x, y} r := by
-- proof
  apply Set.triplewise_pair r

/--
[triplewise_insert](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma triplewise_insert_eq
  {r : α → α → α → Prop}
  {s t : Set α}
  {x y z : α} :
-- imply
  (insert x s).Triplewise r ↔ s.Triplewise r ∧
    ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → r x y z ∧ r y x z ∧ r y z x := by
-- proof
  apply Set.triplewise_insert

/--
[triplewise_insert_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma triplewise_insert_of_not_mem_eq
  {r : α → α → α → Prop}
  {s t : Set α}
  {x y z : α}
-- given
  (hx : x ∉ s) :
-- imply
  (insert x s).Triplewise r ↔ s.Triplewise r ∧
    ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r x y z ∧ r y x z ∧ r y z x := by
-- proof
  apply Set.triplewise_insert_of_not_mem hx

/--
[Triplewise.insert](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma Triplewise_insert_eq
  {r : α → α → α → Prop}
  {s t : Set α}
  {x y z : α}
-- given
  (hs : s.Triplewise r)
  (h : ∀ y ∈ s, ∀ z ∈ s, x ≠ y → x ≠ z → y ≠ z → r x y z ∧ r y x z ∧ r y z x) :
-- imply
  (insert x s).Triplewise r := by
-- proof
  apply Set.Triplewise.insert hs h

/--
[Triplewise.insert_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma Triplewise_insert_of_not_mem_eq
  {r : α → α → α → Prop}
  {s t : Set α}
  {x y z : α}
-- given
  (hx : x ∉ s)
  (hs : s.Triplewise r)
  (h : ∀ y ∈ s, ∀ z ∈ s, y ≠ z → r x y z ∧ r y x z ∧ r y z x) :
-- imply
  (insert x s).Triplewise r := by
-- proof
  apply Set.Triplewise.insert_of_not_mem hx hs h

/--
[triplewise_set_pred_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Data/Set/Triplewise.lean)
-/
@[path]
private lemma triplewise_set_pred_iff_eq
  {S : Set α}
  {P : Set α → Prop} :
-- imply
  S.Triplewise (P {·, ·, ·}) ↔ ∀ T ⊆ S, T.ncard = 3 → P T := by
-- proof
  apply Set.triplewise_set_pred_iff


-- created on 2026-10-20
