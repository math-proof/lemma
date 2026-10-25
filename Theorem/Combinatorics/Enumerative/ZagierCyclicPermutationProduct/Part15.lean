/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part15
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagReturnTime_pos {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) (x : α) :
    0 < zagReturnTime f x :=
  (Nat.find_spec (zagExists_positive_return f x)).1

theorem zagReturnTime_spec {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) (x : α) :
    (f ^ zagReturnTime f x) x = x :=
  (Nat.find_spec (zagExists_positive_return f x)).2

theorem zagReturnTime_no_return {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) (x : α) {r : ℕ}
    (hr0 : 0 < r) (hr : r < zagReturnTime f x) :
    (f ^ r) x ≠ x := by
  intro hreturn
  have hle := Nat.find_min' (zagExists_positive_return f x) ⟨hr0, hreturn⟩
  exact (not_le_of_gt hr) hle

theorem zagTriangle_merge_pow_left {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c : α}
    (hab : ¬f.SameCycle a b) (_hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c) {r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ zagReturnTime f b) :
    ((f * zagTriangle a b c) ^ r) a = (f ^ r) b := by
  let g := f * zagTriangle a b c
  let L := zagReturnTime f b
  induction r using Nat.case_strong_induction_on with
  | hz => omega
  | hi r ih =>
      by_cases hrz : r = 0
      · subst r
        have hab_ne : a ≠ b := fun h => hab (h.sameCycle f)
        have hbc_ne : b ≠ c := fun h => hbc (h.sameCycle f)
        simp [Equiv.Perm.mul_apply,
          zagTriangle_apply_left hab_ne hbc_ne]
      · have hr0' : 0 < r := Nat.pos_of_ne_zero hrz
        have hrlt : r < L := by omega
        have ihr := ih r le_rfl hr0' (by omega)
        have hbr : f.SameCycle b ((f ^ r) b) :=
          ⟨(r : ℤ), by simp⟩
        have hne_b : (f ^ r) b ≠ b :=
          zagReturnTime_no_return f b hr0' hrlt
        have hne_a : (f ^ r) b ≠ a := fun hra =>
          hab (by simpa [hra] using hbr.symm)
        have hne_c : (f ^ r) b ≠ c := fun hrc =>
          hbc (by simpa [hrc] using hbr)
        calc
          (g ^ (r + 1)) a = g ((g ^ r) a) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          _ = g ((f ^ r) b) := by rw [ihr]
          _ = f ((f ^ r) b) := by
            rw [show g = f * zagTriangle a b c by rfl,
              Equiv.Perm.mul_apply,
              zagTriangle_apply_of_ne hne_a hne_b hne_c]
          _ = (f ^ (r + 1)) b := by
            rw [pow_succ', Equiv.Perm.mul_apply]

theorem zagTriangle_merge_pow_middle {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c : α}
    (_hab : ¬f.SameCycle a b) (hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c) {r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ zagReturnTime f c) :
    ((f * zagTriangle a b c) ^ r) b = (f ^ r) c := by
  let g := f * zagTriangle a b c
  let L := zagReturnTime f c
  induction r using Nat.case_strong_induction_on with
  | hz => omega
  | hi r ih =>
      by_cases hrz : r = 0
      · subst r
        simp [Equiv.Perm.mul_apply]
      · have hr0' : 0 < r := Nat.pos_of_ne_zero hrz
        have hrlt : r < L := by omega
        have ihr := ih r le_rfl hr0' (by omega)
        have hcr : f.SameCycle c ((f ^ r) c) :=
          ⟨(r : ℤ), by simp⟩
        have hne_c : (f ^ r) c ≠ c :=
          zagReturnTime_no_return f c hr0' hrlt
        have hne_a : (f ^ r) c ≠ a := fun hra =>
          hac (by simpa [hra] using hcr.symm)
        have hne_b : (f ^ r) c ≠ b := fun hrb =>
          hbc (by simpa [hrb] using hcr.symm)
        calc
          (g ^ (r + 1)) b = g ((g ^ r) b) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          _ = g ((f ^ r) c) := by rw [ihr]
          _ = f ((f ^ r) c) := by
            rw [show g = f * zagTriangle a b c by rfl,
              Equiv.Perm.mul_apply,
              zagTriangle_apply_of_ne hne_a hne_b hne_c]
          _ = (f ^ (r + 1)) c := by
            rw [pow_succ', Equiv.Perm.mul_apply]

theorem zagTriangle_merge_pow_after_left {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c : α}
    (hab : ¬f.SameCycle a b) (hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c) {r : ℕ}
    (hr0 : 0 < r) (hr : r ≤ zagReturnTime f c) :
    ((f * zagTriangle a b c) ^ (zagReturnTime f b + r)) a =
      (f ^ r) c := by
  let g := f * zagTriangle a b c
  have hleft := zagTriangle_merge_pow_left f hab hac hbc
    (zagReturnTime_pos f b) (le_refl (zagReturnTime f b))
  have hmiddle := zagTriangle_merge_pow_middle f hab hac hbc hr0 hr
  calc
    (g ^ (zagReturnTime f b + r)) a =
        (g ^ r) ((g ^ zagReturnTime f b) a) := by
      rw [add_comm, pow_add, Equiv.Perm.mul_apply]
    _ = (g ^ r) b := by rw [hleft, zagReturnTime_spec]
    _ = (f ^ r) c := hmiddle

theorem zagCycleQuotientCount_mul_swap {n : ℕ}
    (f : Equiv.Perm (Fin n)) {x y : Fin n} (hxy_ne : x ≠ y)
    (hxy : f.SameCycle x y) :
    cycleQuotientCount (f * Equiv.swap x y) =
      cycleQuotientCount f + 1 := by
  classical
  let Qf := Quotient (Equiv.Perm.SameCycle.setoid f)
  let Qg := Quotient (Equiv.Perm.SameCycle.setoid (f * Equiv.swap x y))
  let forget : Qg → Qf := Quotient.map id fun {_ _} h =>
    zagSameCycle_mul_swap_refines f hxy h
  have hforget : Function.Surjective forget := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    exact ⟨Quotient.mk _ z, rfl⟩
  have hlower : cycleQuotientCount f ≤
      cycleQuotientCount (f * Equiv.swap x y) := by
    exact Nat.card_le_card_of_surjective forget hforget
  let qx : Qf := Quotient.mk _ x
  let cover : Qf ⊕ Unit → Qg
    | Sum.inl q => if q = qx then Quotient.mk _ x else Quotient.mk _ q.out
    | Sum.inr _ => Quotient.mk _ y
  have hcover : Function.Surjective cover := by
    intro q
    refine Quotient.inductionOn q ?_
    intro z
    by_cases hzx : f.SameCycle z x
    · rcases zagSameCycle_mul_swap_union f hzx.symm with hxz | hyz
      · refine ⟨Sum.inl qx, ?_⟩
        simp only [cover, ite_eq_left rfl]
        exact Quotient.sound hxz
      · refine ⟨Sum.inr (), ?_⟩
        exact Quotient.sound hyz
    · let qz : Qf := Quotient.mk _ z
      have hqz : qz ≠ qx := fun h => hzx (Quotient.exact h)
      refine ⟨Sum.inl qz, ?_⟩
      simp only [cover, ite_eq_right hqz]
      apply Quotient.sound
      have houtz : f.SameCycle qz.out z := by
        change (Equiv.Perm.SameCycle.setoid f).r qz.out z
        apply Quotient.exact
        change (Quotient.mk _ qz.out : Qf) = qz
        exact Quotient.out_eq qz
      have houtx : ¬f.SameCycle qz.out x := fun h =>
        hzx (houtz.symm.trans h)
      exact zagSameCycle_mul_swap_of_not_affected f hxy houtz houtx
  have hupper : cycleQuotientCount (f * Equiv.swap x y) ≤
      cycleQuotientCount f + 1 := by
    have h := Nat.card_le_card_of_surjective cover hcover
    change Nat.card Qg ≤ Nat.card Qf + 1
    simpa only [Nat.card_sum, Nat.card_unique] using h
  have hsign_ne : (f * Equiv.swap x y).sign ≠ f.sign := by
    have hsign : (f * Equiv.swap x y).sign = (-1 : ℤˣ) * f.sign := by
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy_ne]
      ac_rfl
    intro heq
    have hcancel : (-1 : ℤˣ) * f.sign = 1 * f.sign := by
      rw [← hsign, heq, one_mul]
    exact (by decide : (-1 : ℤˣ) ≠ 1) (mul_right_cancel hcancel)
  have hcount_ne : cycleQuotientCount (f * Equiv.swap x y) ≠
      cycleQuotientCount f := by
    intro hcount
    apply hsign_ne
    rw [zagSign_eq_neg_one_pow_cycleCount,
      ← cycleQuotientCount_eq,
      zagSign_eq_neg_one_pow_cycleCount,
      ← cycleQuotientCount_eq, hcount]
  omega

theorem zagMulSwap_not_sameCycle {n : ℕ}
    (f : Equiv.Perm (Fin n)) {x y : Fin n} (hxy_ne : x ≠ y)
    (hxy : f.SameCycle x y) :
    ¬(f * Equiv.swap x y).SameCycle x y := by
  intro hsame
  have hforward := zagCycleQuotientCount_mul_swap f hxy_ne hxy
  have hbackward := zagCycleQuotientCount_mul_swap
    (f * Equiv.swap x y) hxy_ne hsame
  have hundo : (f * Equiv.swap x y) * Equiv.swap x y = f := by
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  rw [hundo, hforward] at hbackward
  omega

theorem zagCycleQuotientCount_mul_triangle {n : ℕ}
    (f : Equiv.Perm (Fin n)) {a b c : Fin n}
    (hac_ne : a ≠ c) (hac : f.SameCycle a c)
    (hab_ne : a ≠ b)
    (hab : (f * Equiv.swap a c).SameCycle a b) :
    cycleQuotientCount (f * zagTriangle a b c) =
      cycleQuotientCount f + 2 := by
  have hfirst := zagCycleQuotientCount_mul_swap f hac_ne hac
  have hsecond := zagCycleQuotientCount_mul_swap
    (f * Equiv.swap a c) hab_ne hab
  simp only [zagTriangle, mul_assoc] at hsecond ⊢
  omega

theorem zagSameCycle_mul_triangle_refines {n : ℕ}
    (f : Equiv.Perm (Fin n)) {a b c x y : Fin n}
    (hac : f.SameCycle a c)
    (hab : (f * Equiv.swap a c).SameCycle a b)
    (hxy : (f * zagTriangle a b c).SameCycle x y) :
    f.SameCycle x y := by
  have hh : (f * Equiv.swap a c).SameCycle x y := by
    simpa only [zagTriangle, mul_assoc] using
      zagSameCycle_mul_swap_refines (f * Equiv.swap a c) hab hxy
  exact zagSameCycle_mul_swap_refines f hac hh

theorem zagTriangle_split_pairwise {n : ℕ}
    (f : Equiv.Perm (Fin n)) {a b c : Fin n}
    (hac_ne : a ≠ c) (hac : f.SameCycle a c)
    (hab_ne : a ≠ b)
    (hab : (f * Equiv.swap a c).SameCycle a b) :
    let g := f * zagTriangle a b c
    ¬g.SameCycle a b ∧ ¬g.SameCycle a c ∧ ¬g.SameCycle b c := by
  let h := f * Equiv.swap a c
  let g := h * Equiv.swap a b
  have hac_h : ¬h.SameCycle a c := by
    exact zagMulSwap_not_sameCycle f hac_ne hac
  have hab_g : ¬g.SameCycle a b := by
    exact zagMulSwap_not_sameCycle h hab_ne hab
  have hrefine (x y : Fin n) (hxy : g.SameCycle x y) : h.SameCycle x y := by
    exact zagSameCycle_mul_swap_refines h hab hxy
  have hac_g : ¬g.SameCycle a c := fun hcycle =>
    hac_h (hrefine a c hcycle)
  have hbc_g : ¬g.SameCycle b c := fun hcycle =>
    hac_h (hab.trans (hrefine b c hcycle))
  simpa only [g, h, zagTriangle, mul_assoc] using
    ⟨hab_g, hac_g, hbc_g⟩

theorem zagNTAE_min_lt_image {n : ℕ} (e π : Equiv.Perm (Fin n))
    {ε : Fin n} (hε : zagNontrivialAntiExceedance e π ε) :
    zagCycleMinPos e π ε < e.symm (π ε) := by
  have hsame : π.SameCycle (π ε) ε :=
    (Equiv.Perm.SameCycle.refl π ε).apply_left
  have hle := zagCycleMinPos_le e π hsame
  apply lt_of_le_of_ne hle
  intro heq
  apply hε.2
  simp only [zagTrivialAntiExceedance]
  exact e.symm.injective (by simpa using heq.symm)

theorem zagNTAE_image_lt {n : ℕ} (e π : Equiv.Perm (Fin n))
    {ε : Fin n} (hε : zagNontrivialAntiExceedance e π ε) :
    e.symm (π ε) < e.symm ε := by
  have hle : e.symm (π ε) ≤ e.symm ε := by
    exact not_lt.mp hε.1
  apply lt_of_le_of_ne hle
  intro heq
  have hfix : π ε = ε := e.symm.injective heq
  apply hε.2
  simp only [zagTrivialAntiExceedance]
  have hmin := zagCycleMinPos_mem e π ε
  have hlabel : e (zagCycleMinPos e π ε) = ε :=
    hmin.eq_of_right hfix
  exact hfix.trans hlabel.symm

end MetaMathlibExt
