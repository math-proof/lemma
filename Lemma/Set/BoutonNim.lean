import Mathlib
import Initialize.Tactic.Attr.Basic


namespace MetaMathlibExt.BoutonNim

/--
[foldl_xor_init](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BoutonNim.lean)
-/
@[path]
private lemma foldl_xor_init (l : List ℕ) (init : ℕ) :
  List.foldl Nat.xor init l = init ^^^ List.foldl Nat.xor 0 l := by
  revert init
  induction l with
  | nil =>
    intro init
    exact (Nat.xor_zero init).symm
  | cons a t ih =>
    intro init
    have hz : Nat.xor 0 a = a := Nat.zero_xor a
    have e3 : List.foldl Nat.xor 0 (a :: t) = (a ^^^ List.foldl Nat.xor 0 t) := by
      calc List.foldl Nat.xor 0 (a :: t)
        = List.foldl Nat.xor (Nat.xor 0 a) t := rfl
        _ = List.foldl Nat.xor a t := by rw [hz]
        _ = (a ^^^ List.foldl Nat.xor 0 t) := ih a
    calc List.foldl Nat.xor init (a :: t)
      = List.foldl Nat.xor (Nat.xor init a) t := rfl
      _ = (Nat.xor init a) ^^^ List.foldl Nat.xor 0 t := ih _
      _ = init ^^^ (a ^^^ List.foldl Nat.xor 0 t) := Nat.xor_assoc _ _ _
      _ = init ^^^ List.foldl Nat.xor 0 (a :: t) := by rw [e3]

end MetaMathlibExt.BoutonNim

namespace MetaMathlibExt.BoutonNim

/--
[cons_fold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BoutonNim.lean)
-/
@[path]
private lemma cons_fold (a : ℕ) (s : List ℕ) :
  List.foldl Nat.xor 0 (a :: s) = (a ^^^ List.foldl Nat.xor 0 s) := by
  have hz : Nat.xor 0 a = a := Nat.zero_xor a
  calc List.foldl Nat.xor 0 (a :: s)
    = List.foldl Nat.xor (Nat.xor 0 a) s := rfl
    _ = List.foldl Nat.xor a s := by rw [hz]
    _ = (a ^^^ List.foldl Nat.xor 0 s) := foldl_xor_init s a

end MetaMathlibExt.BoutonNim

namespace MetaMathlibExt.BoutonNim

/--
[foldl_set](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BoutonNim.lean)
-/
@[path]
private lemma foldl_set (pos : List ℕ) (idx y : ℕ) (h : idx < pos.length) :
  List.foldl Nat.xor 0 (pos.set idx y)
    = (List.foldl Nat.xor 0 pos ^^^ pos[idx]'h ^^^ y) := by
  revert h
  revert idx
  induction pos with
  | nil =>
    intro idx h
    simp at h
  | cons a t ih =>
    intro idx h
    cases idx with
    | zero =>
      have hs : (a :: t).set 0 y = y :: t := rfl
      have hg : (a :: t)[0]'h = a := List.getElem_cons_zero _ _ _
      simp only [hs, hg, cons_fold]
      have key : ((a ^^^ List.foldl Nat.xor 0 t) ^^^ a)
        = List.foldl Nat.xor 0 t := by
        calc ((a ^^^ List.foldl Nat.xor 0 t) ^^^ a)
          = a ^^^ (List.foldl Nat.xor 0 t ^^^ a) := Nat.xor_assoc _ _ _
          _ = a ^^^ (a ^^^ List.foldl Nat.xor 0 t) := by
            rw [Nat.xor_comm (List.foldl Nat.xor 0 t) a]
          _ = (a ^^^ a) ^^^ List.foldl Nat.xor 0 t := (Nat.xor_assoc _ _ _).symm
          _ = List.foldl Nat.xor 0 t := by rw [Nat.xor_self, Nat.zero_xor]
      rw [key]
      exact Nat.xor_comm _ _
    | succ n =>
      have hlen : (a :: t).length = t.length + 1 := rfl
      have h' : n < t.length := by
        rw [hlen] at h
        exact Nat.lt_of_succ_lt_succ h
      have hs : (a :: t).set (n + 1) y = a :: (t.set n y) := rfl
      have hg : (a :: t)[n + 1]'h = t[n]'h' := List.getElem_cons_succ _ _ _ _
      have ih' := ih n h'
      simp only [hs, hg, cons_fold, ih']
      rw [Nat.xor_assoc a _ _, ← Nat.xor_assoc a _ _]

end MetaMathlibExt.BoutonNim

namespace MetaMathlibExt.BoutonNim

/--
[foldl_testBit_false](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BoutonNim.lean)
-/
@[path]
private lemma foldl_testBit_false : ∀ (l : List ℕ) (k : ℕ),
  (∀ x ∈ l, x.testBit k = false) →
  (List.foldl Nat.xor 0 l).testBit k = false := by
  intro l k
  induction l with
  | nil =>
    intro hall
    exact Nat.zero_testBit k
  | cons a t ih =>
    intro hall
    have ha : a.testBit k = false := hall a (by simp)
    have ht : ∀ x ∈ t, x.testBit k = false :=
      fun x hx => hall x (List.mem_cons_of_mem _ hx)
    have e := ih ht
    rw [cons_fold a t, Nat.testBit_xor, ha, e, Bool.false_xor]

end MetaMathlibExt.BoutonNim

namespace MetaMathlibExt.BoutonNim

/--
[xor_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BoutonNim.lean)
-/
@[path]
private lemma xor_eq_zero_iff (a b : ℕ) : (a ^^^ b = 0) ↔ a = b := by
  constructor
  · intro h
    have h2 : (a ^^^ b) ^^^ b = a := by
      calc (a ^^^ b) ^^^ b
        = a ^^^ (b ^^^ b) := Nat.xor_assoc _ _ _
        _ = a := by rw [Nat.xor_self, Nat.xor_zero]
    rwa [h, Nat.zero_xor] at h2
  · intro h
    subst h
    exact Nat.xor_self _

end MetaMathlibExt.BoutonNim

namespace MetaMathlibExt.BoutonNim

/--
[foldl_set_fin](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BoutonNim.lean)
-/
@[path]
private theorem foldl_set_fin (pos : List ℕ) (i : Fin pos.length) (y : ℕ) :
  List.foldl Nat.xor 0 (pos.set i.val y)
    = (List.foldl Nat.xor 0 pos ^^^ pos.get i ^^^ y) := by
  have h := foldl_set pos i.val y i.isLt
  rwa [List.get_eq_getElem]

end MetaMathlibExt.BoutonNim

namespace MetaMathlibExt.BoutonNim

/--
[bouton_nim_p_positions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BoutonNim.lean)
-/
@[path]
lemma bouton_nim_p_positions
  {pos : List ℕ} :
-- imply
  (List.foldl Nat.xor 0 pos = 0 →
    ∀ (i : Fin pos.length) (y : ℕ), y < pos.get i →
    List.foldl Nat.xor 0 (pos.set i.val y) ≠ 0) ∧
    (List.foldl Nat.xor 0 pos ≠ 0 →
    ∃ (i : Fin pos.length) (y : ℕ), y < pos.get i ∧
    List.foldl Nat.xor 0 (pos.set i.val y) = 0) := by
-- proof
  constructor
  · intro hs0 i y hylt hcon
    have hset := foldl_set_fin pos i y
    rw [hs0, Nat.zero_xor] at hset
    have h0 : pos.get i ^^^ y = 0 := hset.symm.trans hcon
    have heq : pos.get i = y := (xor_eq_zero_iff _ _).mp h0
    exact (ne_of_lt hylt) heq.symm
  · intro hne
    obtain ⟨k, hk_true, hk_above⟩ := Nat.exists_most_significant_bit hne
    have hex : ∃ x ∈ pos, x.testBit k = true := by
      by_contra habs
      push Not at habs
      have hfalse :=
        foldl_testBit_false pos k (fun x hx => by simpa using habs x hx)
      rw [hk_true] at hfalse
      exact Bool.noConfusion hfalse
    obtain ⟨x, hx_mem, hx_bit⟩ := hex
    obtain ⟨i, hi_eq⟩ := List.mem_iff_get.mp hx_mem
    refine ⟨i, List.foldl Nat.xor 0 pos ^^^ pos.get i, ?_, ?_⟩
    · have hx_bit' : (pos.get i).testBit k = true := by
      rwa [hi_eq]
      have hy_bit : (List.foldl Nat.xor 0 pos ^^^ pos.get i).testBit k = false := by
        rw [Nat.testBit_xor, hk_true, hx_bit']
        rfl
      have hagree : ∀ j, k < j →
        (List.foldl Nat.xor 0 pos ^^^ pos.get i).testBit j
          = (pos.get i).testBit j := by
        intro j hj
        rw [Nat.testBit_xor, hk_above j hj, Bool.false_xor]
      exact Nat.lt_of_testBit k hy_bit hx_bit' hagree
    · have hset :=
      foldl_set_fin pos i (List.foldl Nat.xor 0 pos ^^^ pos.get i)
      rw [hset]
      exact Nat.xor_self _

end MetaMathlibExt.BoutonNim


-- created on 2026-10-20
-- updated on 2026-10-26
