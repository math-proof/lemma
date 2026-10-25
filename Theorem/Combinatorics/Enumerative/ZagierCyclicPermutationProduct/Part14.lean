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
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part14
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagVertical_blockSwap {n : ℕ} (D e : Equiv.Perm (Fin n))
    (a b c : Fin n) (hab : a < b) (hbc : b < c) :
    zagVertical D (e * zagBlockSwap a b c hab hbc) =
      zagVertical D e * zagTriangle (e a) (e b) (e c) := by
  simp only [zagVertical, zagHorizontal_blockSwap]
  group

theorem zagSameCycle_of_step {α : Type*} [Finite α]
    (f g : Equiv.Perm α)
    (hstep : ∀ z, f.SameCycle z (g z)) {a b : α}
    (hab : g.SameCycle a b) : f.SameCycle a b := by
  obtain ⟨m, hm⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ r : ℕ, f.SameCycle a ((g ^ r) a) := by
    intro r
    induction r with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        exact ih.trans (by simpa [pow_succ'] using hstep ((g ^ r) a))
  simpa [hm] using hpow m

theorem zagSameCycle_mul_swap_refines {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {x y a b : α}
    (hxy : f.SameCycle x y)
    (hab : (f * Equiv.swap x y).SameCycle a b) :
    f.SameCycle a b := by
  apply zagSameCycle_of_step f (f * Equiv.swap x y) _ hab
  intro z
  have hz : f.SameCycle z (Equiv.swap x y z) := by
    rw [Equiv.swap_apply_def]
    split_ifs with hzx hzy
    · simpa [hzx] using hxy
    · simpa [hzy] using hxy.symm
    · exact Equiv.Perm.SameCycle.rfl
  exact hz.trans (by
    simpa [Equiv.Perm.mul_apply] using
      (Equiv.Perm.SameCycle.refl f (Equiv.swap x y z)).apply_right)

theorem zagSameCycle_mul_swap_of_not_affected {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {x y a b : α}
    (hxy : f.SameCycle x y) (hab : f.SameCycle a b)
    (hax : ¬f.SameCycle a x) :
    (f * Equiv.swap x y).SameCycle a b := by
  obtain ⟨m, hm⟩ := hab.exists_nat_pow_eq
  have hpow : ∀ r : ℕ, (f * Equiv.swap x y).SameCycle a ((f ^ r) a) := by
    intro r
    induction r with
    | zero => exact Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        let z := (f ^ r) a
        have haz : f.SameCycle a z := by
          exact ⟨(r : ℤ), by simp [z]⟩
        have hzx : z ≠ x := fun h => hax (by simpa [h] using haz)
        have hzy : z ≠ y := fun h => hax (haz.trans (by simpa [h] using hxy.symm))
        have hstep : (f * Equiv.swap x y) z = f z := by
          simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hzx hzy]
        have hrel : (f * Equiv.swap x y).SameCycle z (f z) := by
          rw [← hstep]
          exact (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) z).apply_right
        exact ih.trans (by simpa [z, pow_succ', Equiv.Perm.mul_apply] using hrel)
  simpa [hm] using hpow m

theorem zagSameCycle_mul_swap_iff_of_disjoint {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b x y : α}
    (hxa : ¬f.SameCycle x a) (hxb : ¬f.SameCycle x b) :
    (f * Equiv.swap a b).SameCycle x y ↔ f.SameCycle x y := by
  let g := f * Equiv.swap a b
  have hpow (r : ℕ) : (g ^ r) x = (f ^ r) x := by
    induction r with
    | zero => rfl
    | succ r ih =>
        have hcycle : f.SameCycle x ((f ^ r) x) :=
          ⟨(r : ℤ), by simp⟩
        have hne_a : (f ^ r) x ≠ a := fun h => hxa (by simpa [h] using hcycle)
        have hne_b : (f ^ r) x ≠ b := fun h => hxb (by simpa [h] using hcycle)
        rw [pow_succ', pow_succ', Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
        simp only [Equiv.Perm.mul_apply,
          Equiv.swap_apply_of_ne_of_ne hne_a hne_b]
  constructor
  · intro hxy
    obtain ⟨r, hr⟩ := hxy.exists_nat_pow_eq
    exact ⟨(r : ℤ), by rw [zpow_natCast, ← hpow]; exact hr⟩
  · intro hxy
    obtain ⟨r, hr⟩ := hxy.exists_nat_pow_eq
    exact ⟨(r : ℤ), by rw [zpow_natCast, hpow]; exact hr⟩

theorem zagSameCycle_mul_triangle_iff_of_disjoint {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c x y : α}
    (hxa : ¬f.SameCycle x a) (hxb : ¬f.SameCycle x b)
    (hxc : ¬f.SameCycle x c) :
    (f * zagTriangle a b c).SameCycle x y ↔ f.SameCycle x y := by
  let g := f * Equiv.swap a c
  have hg : ∀ z, g.SameCycle x z ↔ f.SameCycle x z := fun z =>
    zagSameCycle_mul_swap_iff_of_disjoint f hxa hxc
  have hga : ¬g.SameCycle x a := fun h => hxa ((hg a).mp h)
  have hgb : ¬g.SameCycle x b := fun h => hxb ((hg b).mp h)
  calc
    (f * zagTriangle a b c).SameCycle x y ↔
        (g * Equiv.swap a b).SameCycle x y := by
      simp only [g, zagTriangle, mul_assoc]
    _ ↔ g.SameCycle x y :=
      zagSameCycle_mul_swap_iff_of_disjoint g hga hgb
    _ ↔ f.SameCycle x y := hg y

theorem zagMulSwap_sameCycle_of_not_sameCycle {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {x y : α}
    (hxy : ¬f.SameCycle x y) :
    (f * Equiv.swap x y).SameCycle x y := by
  let returns (m : ℕ) : Prop := 0 < m ∧ (f ^ m) y = y
  have hex : ∃ m, returns m := by
    refine ⟨orderOf f, orderOf_pos f, ?_⟩
    rw [pow_orderOf_eq_one]
    rfl
  let m := Nat.find hex
  have hm : returns m := Nat.find_spec hex
  let g := f * Equiv.swap x y
  have hpow (r : ℕ) (hr : r < m) :
      (g ^ (r + 1)) x = (f ^ (r + 1)) y := by
    induction r with
    | zero => simp [g, Equiv.Perm.mul_apply]
    | succ r ih =>
        have hrm : r < m := by omega
        have hne_y : (f ^ (r + 1)) y ≠ y := by
          intro heq
          have hle := Nat.find_min' hex ⟨by omega, heq⟩
          omega
        have hne_x : (f ^ (r + 1)) y ≠ x := by
          intro heq
          apply hxy
          have hyx : f.SameCycle y x :=
            ⟨((r + 1 : ℕ) : ℤ), by rw [zpow_natCast]; exact heq⟩
          exact hyx.symm
        calc
          (g ^ (r + 1 + 1)) x = g ((g ^ (r + 1)) x) := by
            rw [pow_succ', Equiv.Perm.mul_apply]
          _ = g ((f ^ (r + 1)) y) := by rw [ih hrm]
          _ = f ((f ^ (r + 1)) y) := by
            simp only [g, Equiv.Perm.mul_apply]
            rw [Equiv.swap_apply_of_ne_of_ne hne_x hne_y]
          _ = (f ^ (r + 1 + 1)) y := by
            simp [pow_succ', Equiv.Perm.mul_apply]
  have hlt : m - 1 < m := by omega
  have hlast := hpow (m - 1) hlt
  have hsub : m - 1 + 1 = m := by omega
  rw [hsub, hm.2] at hlast
  exact ⟨(m : ℤ), by simpa using hlast⟩

theorem zagSameCycle_mul_swap_union {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {x y z : α}
    (hz : f.SameCycle x z) :
    (f * Equiv.swap x y).SameCycle x z ∨
      (f * Equiv.swap x y).SameCycle y z := by
  obtain ⟨m, hm⟩ := hz.exists_nat_pow_eq
  have hpow : ∀ r : ℕ,
      (f * Equiv.swap x y).SameCycle x ((f ^ r) x) ∨
        (f * Equiv.swap x y).SameCycle y ((f ^ r) x) := by
    intro r
    induction r with
    | zero => exact Or.inl Equiv.Perm.SameCycle.rfl
    | succ r ih =>
        let w := (f ^ r) x
        by_cases hwx : w = x
        · right
          have hstep : (f * Equiv.swap x y) y = f x := by
            simp [Equiv.Perm.mul_apply]
          have hrel :=
            (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) y).apply_right
          simpa [pow_succ', w, Equiv.Perm.mul_apply, hstep, hwx] using hrel
        · by_cases hwy : w = y
          · left
            have hstep : (f * Equiv.swap x y) x = f y := by
              simp [Equiv.Perm.mul_apply]
            have hrel :=
              (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) x).apply_right
            simpa [pow_succ', w, Equiv.Perm.mul_apply, hstep, hwy] using hrel
          · have hstep : (f * Equiv.swap x y) w = f w := by
              simp [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hwx hwy]
            rcases ih with hxw | hyw
            · left
              have hrel : (f * Equiv.swap x y).SameCycle w (f w) := by
                rw [← hstep]
                exact (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) w).apply_right
              exact hxw.trans (by
                simpa [w, pow_succ', Equiv.Perm.mul_apply] using hrel)
            · right
              have hrel : (f * Equiv.swap x y).SameCycle w (f w) := by
                rw [← hstep]
                exact (Equiv.Perm.SameCycle.refl (f * Equiv.swap x y) w).apply_right
              exact hyw.trans (by
                simpa [w, pow_succ', Equiv.Perm.mul_apply] using hrel)
  simpa [hm] using hpow m

theorem zagTriangle_merge_sameCycles {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c : α}
    (hab : ¬f.SameCycle a b) (hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c) :
    let g := f * zagTriangle a b c
    g.SameCycle a b ∧ g.SameCycle a c := by
  let h := f * Equiv.swap a c
  have hac_h : h.SameCycle a c :=
    zagMulSwap_sameCycle_of_not_sameCycle f hac
  have hab_h : ¬h.SameCycle a b := by
    intro hab_h'
    have hu := zagSameCycle_mul_swap_union (f := h)
      (x := a) (y := c) (z := b) hab_h'
    have hundo : h * Equiv.swap a c = f := by
      simp [h, mul_assoc]
    rw [hundo] at hu
    rcases hu with hab' | hcb'
    · exact hab hab'
    · exact hbc hcb'.symm
  let g := h * Equiv.swap a b
  have hab_g : g.SameCycle a b :=
    zagMulSwap_sameCycle_of_not_sameCycle h hab_h
  have hac_or : g.SameCycle a c ∨ g.SameCycle b c :=
    zagSameCycle_mul_swap_union (f := h)
      (x := a) (y := b) (z := c) hac_h
  have hac_g : g.SameCycle a c := hac_or.elim id (fun hbc' => hab_g.trans hbc')
  simpa only [g, h, zagTriangle, mul_assoc] using ⟨hab_g, hac_g⟩

theorem zagTriangle_merge_cases {α : Type*} [Finite α]
    [DecidableEq α] (f : Equiv.Perm α) {a b c x : α}
    (hab : ¬f.SameCycle a b) (hac : ¬f.SameCycle a c)
    (hbc : ¬f.SameCycle b c)
    (hx : (f * zagTriangle a b c).SameCycle a x) :
    f.SameCycle a x ∨ f.SameCycle b x ∨ f.SameCycle c x := by
  let h := f * Equiv.swap a c
  let g := h * Equiv.swap a b
  have hac_h : h.SameCycle a c :=
    zagMulSwap_sameCycle_of_not_sameCycle f hac
  have hab_h : ¬h.SameCycle a b := by
    intro hab_h'
    have hu := zagSameCycle_mul_swap_union (f := h)
      (x := a) (y := c) (z := b) hab_h'
    have hundo : h * Equiv.swap a c = f := by simp [h, mul_assoc]
    rw [hundo] at hu
    rcases hu with hab' | hcb'
    · exact hab hab'
    · exact hbc hcb'.symm
  have hxg : g.SameCycle a x := by
    simpa only [g, h, zagTriangle, mul_assoc] using hx
  have hsplit := zagSameCycle_mul_swap_union (f := g)
    (x := a) (y := b) (z := x) hxg
  have hgundo : g * Equiv.swap a b = h := by simp [g, mul_assoc]
  rw [hgundo] at hsplit
  rcases hsplit with hax | hbx
  · have hsplit' := zagSameCycle_mul_swap_union (f := h)
      (x := a) (y := c) (z := x) hax
    have hhundo : h * Equiv.swap a c = f := by simp [h, mul_assoc]
    rw [hhundo] at hsplit'
    exact hsplit'.elim Or.inl (fun hcx => Or.inr (Or.inr hcx))
  · right
    left
    have hnot : ¬h.SameCycle b a := fun hba => hab_h hba.symm
    have hpres := zagSameCycle_mul_swap_of_not_affected h hac_h hbx hnot
    have hhundo : h * Equiv.swap a c = f := by simp [h, mul_assoc]
    rwa [hhundo] at hpres

theorem zagExists_positive_return {α : Type*} [Finite α]
    (f : Equiv.Perm α) (x : α) :
    ∃ m : ℕ, 0 < m ∧ (f ^ m) x = x := by
  refine ⟨orderOf f, orderOf_pos f, ?_⟩
  rw [pow_orderOf_eq_one]
  rfl

end MetaMathlibExt
