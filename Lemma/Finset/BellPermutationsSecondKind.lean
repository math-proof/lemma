import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.BellPermutationsSecondKind
open MetaMathlibExt


namespace MetaMathlibExt

/--
[pp_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma pp_zero {n : ℕ} (f : Fin n → Fin n) : pp f 0 = 1 := by
  simp [pp]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pp_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma pp_succ {n : ℕ} (f : Fin n → Fin n) {m : ℕ} (h : m < n) :
  pp f (m+1) = pp f m * Equiv.swap ⟨m, h⟩ (f ⟨m, h⟩) := by
  have hlen : m < (List.finRange n).length := by simpa using h
  have : (List.finRange n).take (m+1) = (List.finRange n).take m ++ [(⟨m, h⟩ : Fin n)] := by
    rw [List.take_add_one]
    congr 1
    rw [List.getElem?_eq_getElem hlen, List.getElem_finRange]
    simp
  unfold pp
  rw [this, List.map_append, List.prod_append]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pp_full](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma pp_full {n : ℕ} (f : Fin n → Fin n) : pp f n = bellPerm f := by
  unfold pp bellPerm
  rw [List.take_of_length_le (by simp)]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pp_fixes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma pp_fixes {n : ℕ} {f : Fin n → Fin n} (hf : Subdiag f) :
  ∀ (m : ℕ) (j : Fin n), m ≤ j.val → pp f m j = j := by
  intro m
  induction m with
  | zero => intro j _; rw [pp_zero]; rfl
  | succ m ih =>
    intro j hj
    have hmn : m < n := by have := j.isLt; omega
    rw [pp_succ f hmn, Equiv.Perm.mul_apply]
    have hne1 : j ≠ (⟨m, hmn⟩ : Fin n) := by
      intro hc
      have : j.val = m := by rw [hc]
      omega
    have hne2 : j ≠ f ⟨m, hmn⟩ := by
      intro hc
      have h1 : (f ⟨m, hmn⟩).val ≤ m := hf ⟨m, hmn⟩
      have : j.val = (f ⟨m, hmn⟩).val := by rw [hc]
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hne1 hne2]
    exact ih j (by omega)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pp_succ_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma pp_succ_apply {n : ℕ} {f : Fin n → Fin n} (hf : Subdiag f) {m : ℕ} (h : m < n) :
  pp f (m+1) (f ⟨m, h⟩) = ⟨m, h⟩ := by
  rw [pp_succ f h, Equiv.Perm.mul_apply, Equiv.swap_apply_right]
  exact pp_fixes hf m ⟨m, h⟩ (le_refl m)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[pp_eq_imp](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma pp_eq_imp {n : ℕ} {f g : Fin n → Fin n} (hf : Subdiag f) (hg : Subdiag g) :
  ∀ (m : ℕ), m ≤ n → pp f m = pp g m → ∀ i : Fin n, i.val < m → f i = g i := by
  intro m
  induction m with
  | zero => intro _ _ i hi; omega
  | succ m ih =>
    intro hmn heq i hi
    have hm : m < n := by omega
    have e1 : pp f (m+1) (f ⟨m, hm⟩) = ⟨m, hm⟩ := pp_succ_apply hf hm
    have e2 : pp g (m+1) (g ⟨m, hm⟩) = ⟨m, hm⟩ := pp_succ_apply hg hm
    have e2' : pp f (m+1) (g ⟨m, hm⟩) = ⟨m, hm⟩ := by rw [heq]; exact e2
    have htop : f ⟨m, hm⟩ = g ⟨m, hm⟩ := (pp f (m+1)).injective (e1.trans e2'.symm)
    have hswap : Equiv.swap (⟨m, hm⟩ : Fin n) (f ⟨m, hm⟩) = Equiv.swap ⟨m, hm⟩ (g ⟨m, hm⟩) := by
      rw [htop]
    have hppm : pp f m = pp g m := by
      rw [pp_succ f hm, pp_succ g hm, hswap] at heq
      exact mul_right_cancel heq
    obtain hlt | heqi := Nat.lt_succ_iff_lt_or_eq.mp hi
    · exact ih (by omega) hppm i hlt
    · have : i = ⟨m, hm⟩ := Fin.ext (by omega)
      rw [this]; exact htop

end MetaMathlibExt

namespace MetaMathlibExt

/--
[bellPerm_inj_subdiag](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma bellPerm_inj_subdiag {n : ℕ} {f g : Fin n → Fin n} (hf : Subdiag f) (hg : Subdiag g)
  (h : bellPerm f = bellPerm g) : f = g := by
  have hn : pp f n = pp g n := by rw [pp_full, pp_full]; exact h
  funext i
  exact pp_eq_imp hf hg n (le_refl n) hn i i.isLt

end MetaMathlibExt

namespace MetaMathlibExt

/--
[qq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma qq_zero {n : ℕ} (f : Fin n → Fin n) : qq f 0 = bellPerm f := by
  simp [qq, bellPerm]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[qq_ge](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma qq_ge {n : ℕ} (f : Fin n → Fin n) {m : ℕ} (h : n ≤ m) : qq f m = 1 := by
  unfold qq
  rw [List.drop_of_length_le (by simpa using h)]
  simp

end MetaMathlibExt

namespace MetaMathlibExt

/--
[qq_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma qq_succ {n : ℕ} (f : Fin n → Fin n) {m : ℕ} (h : m < n) :
  qq f m = Equiv.swap ⟨m, h⟩ (f ⟨m, h⟩) * qq f (m+1) := by
  have hlen : m < (List.finRange n).length := by simpa using h
  have hdrop : (List.finRange n).drop m = (⟨m, h⟩ : Fin n) :: (List.finRange n).drop (m+1) := by
    rw [List.drop_eq_getElem_cons hlen, List.getElem_finRange]
    simp
  unfold qq
  rw [hdrop, List.map_cons, List.prod_cons]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[qq_fix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma qq_fix {n : ℕ} (f : Fin n → Fin n) (y : Fin n) :
  ∀ d m : ℕ, n - m ≤ d → (∀ i : Fin n, m ≤ i.val → y ≠ i ∧ y ≠ f i) → qq f m y = y := by
  intro d
  induction d with
  | zero => intro m hm _; rw [qq_ge f (by omega)]; rfl
  | succ d ih =>
    intro m hm H
    by_cases hmn : n ≤ m
    · rw [qq_ge f hmn]; rfl
    · rw [not_le] at hmn
      rw [qq_succ f hmn, Equiv.Perm.mul_apply]
      have hrec : qq f (m+1) y = y := ih (m+1) (by omega) (fun i hi => H i (by omega))
      rw [hrec]
      obtain ⟨h1, h2⟩ := H ⟨m, hmn⟩ (le_refl m)
      exact Equiv.swap_apply_of_ne_of_ne h1 h2

end MetaMathlibExt

namespace MetaMathlibExt

/--
[qq_lower_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma qq_lower_const {n : ℕ} (f : Fin n → Fin n) (y z : Fin n) (m0 : ℕ) (hm0 : m0 < n)
  (hz : qq f m0 y = z) (Hfix : ∀ i : Fin n, i.val < m0 → z ≠ i ∧ z ≠ f i) :
  qq f 0 y = z := by
  have key : ∀ d m, m0 - m ≤ d → m ≤ m0 → qq f m y = z := by
    intro d
    induction d with
    | zero =>
      intro m h1 h2
      obtain rfl : m = m0 := by omega
      exact hz
    | succ d ih =>
      intro m h1 h2
      obtain heq | hlt := eq_or_lt_of_le h2
      · subst heq; exact hz
      · have hmn : m < n := by omega
        rw [qq_succ f hmn, Equiv.Perm.mul_apply, ih (m+1) (by omega) (by omega)]
        obtain ⟨ha, hb⟩ := Hfix ⟨m, hmn⟩ hlt
        exact Equiv.swap_apply_of_ne_of_ne ha hb
  exact key m0 0 (by omega) (by omega)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sigma_ge_of_value](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma sigma_ge_of_value {n : ℕ} {f : Fin n → Fin n} (hf : Subdiag f) (v : Fin n)
  (hv : ∃ j, f j = v) : v ≤ bellPerm f v := by
  classical
  let S : Finset (Fin n) := Finset.univ.filter (fun i => f i = v)
  have hSne : S.Nonempty := by obtain ⟨j, hj⟩ := hv; exact ⟨j, by simp [S, hj]⟩
  let mp := S.max' hSne
  have hmpf : f mp = v := by
    have : mp ∈ S := S.max'_mem hSne
    simpa [S] using this
  have hmpmax : ∀ i, f i = v → i ≤ mp := by
    intro i hi; exact S.le_max' i (by simp [S, hi])
  have hvmp : v.val ≤ mp.val := by
    have := hf mp; rw [hmpf] at this; exact this
  have fixhi : qq f (mp.val + 1) v = v := by
    apply qq_fix f v n (mp.val + 1) (by omega)
    intro i hi
    constructor
    · intro hc; rw [← hc] at hi; omega
    · intro hc
      have := hmpmax i hc.symm
      have : i.val ≤ mp.val := this
      omega
  have hbase : qq f mp.val v = mp := by
    have hmn : mp.val < n := mp.isLt
    rw [qq_succ f hmn, Equiv.Perm.mul_apply, fixhi]
    have hmm : (⟨mp.val, hmn⟩ : Fin n) = mp := Fin.ext rfl
    rw [hmm, hmpf, Equiv.swap_apply_right]
  have hσ : bellPerm f v = mp := by
    rw [← qq_zero]
    apply qq_lower_const f v mp mp.val mp.isLt hbase
    intro i hi
    constructor
    · intro hc; rw [hc] at hi; omega
    · intro hc
      have hle := hf i
      rw [← hc] at hle
      have : mp.val ≤ i.val := hle
      omega
  rwa [hσ]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[sigma_lt_of_novalue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma sigma_lt_of_novalue {n : ℕ} {f : Fin n → Fin n} (x : Fin n)
  (Hlt : ∀ i : Fin n, (f i).val < x.val) : (bellPerm f x).val < x.val := by
  have fixhi : qq f (x.val + 1) x = x := by
    apply qq_fix f x n (x.val + 1) (by omega)
    intro i hi
    refine ⟨?_, ?_⟩
    · intro hc; rw [← hc] at hi; omega
    · intro hc; have := Hlt i; rw [hc] at this; omega
  have hbase : (qq f x.val x).val < x.val := by
    have hxn := x.isLt
    rw [qq_succ f hxn, Equiv.Perm.mul_apply, fixhi]
    have hxx : (⟨x.val, hxn⟩ : Fin n) = x := Fin.ext rfl
    rw [hxx, Equiv.swap_apply_left]
    exact Hlt x
  have key : ∀ d m, x.val - m ≤ d → m ≤ x.val → (qq f m x).val < x.val := by
    intro d
    induction d with
    | zero =>
      intro m h1 h2
      obtain rfl : m = x.val := by omega
      exact hbase
    | succ d ih =>
      intro m h1 h2
      obtain heq | hlt := eq_or_lt_of_le h2
      · rw [heq]; exact hbase
      · have hmn : m < n := by omega
        rw [qq_succ f hmn, Equiv.Perm.mul_apply]
        have hw : (qq f (m+1) x).val < x.val := ih (m+1) (by omega) (by omega)
        obtain h | h := eq_or_ne (qq f (m+1) x) ⟨m, hmn⟩
        · rw [h, Equiv.swap_apply_left]; exact Hlt _
        obtain h' | h' := eq_or_ne (qq f (m+1) x) (f ⟨m, hmn⟩)
        · rw [h', Equiv.swap_apply_right]; exact hlt
        · rw [Equiv.swap_apply_of_ne_of_ne h h']; exact hw
  have := key x.val 0 (by omega) (by omega)
  rwa [qq_zero] at this

end MetaMathlibExt

namespace MetaMathlibExt

/--
[rgf_novalue_lt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma rgf_novalue_lt {n : ℕ} {f : Fin n → Fin n} (hf : IsRGF f) (x : Fin n)
  (hx : ∀ j, f j ≠ x) : ∀ j, (f j).val < x.val := by
  intro j
  obtain h | h | h := lt_trichotomy (f j).val x.val
  · exact h
  · exact absurd (Fin.ext h) (hx j)
  · obtain ⟨i0, _, hi0⟩ := hf j x h
    exact absurd hi0 (hx i0)

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_A_0_0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma card_A_0_0 : Nat.card (Asub 0 0) = 1 := by
  have : Unique (Asub 0 0) :=
    { default := ⟨Fin.elim0, fun i => i.elim0, by simp [numVals]⟩
      uniq := fun a => Subtype.ext (funext (fun i => i.elim0)) }
  exact Nat.card_unique

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_A_succ_0](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma card_A_succ_0 (n : ℕ) : Nat.card (Asub (n+1) 0) = 0 := by
  have : IsEmpty (Asub (n+1) 0) :=
    ⟨fun p => by
      obtain ⟨f, _, hn⟩ := p
      have hne : (Finset.univ.image f).Nonempty :=
        ⟨f ⟨0, Nat.succ_pos n⟩, Finset.mem_image_of_mem f (Finset.mem_univ _)⟩
      have := Finset.Nonempty.card_pos hne
      simp only [numVals] at hn
      omega⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)

end MetaMathlibExt

/--
[bell_perm_second_kind_weakExcedance_eq_stirlingSecond](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/BellPermutationsSecondKind.lean)
-/
@[path]
private lemma bell_perm_second_kind_weakExcedance_eq_stirlingSecond_eq
  {n k : ℕ}
-- given
  (hn : 0 < n) :
-- imply
  let IsRGF : (Fin n → Fin n) → Prop := by
-- proof
  apply MetaMathlibExt.bell_perm_second_kind_weakExcedance_eq_stirlingSecond n k hn


-- created on 2026-10-20
-- updated on 2026-10-23
