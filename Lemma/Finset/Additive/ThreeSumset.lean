import Mathlib
import sympy.Basic
import Def.Combinatorics.Additive.ThreeSumset.Part3
open scoped Pointwise
open MetaMathlibExt


namespace MetaMathlibExt

/--
[mem_reps_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean)
-/
@[path]
private lemma mem_reps_iff {G : Type*} [DecidableEq G] [Add G]
  {A B C : Finset G} {s : G} {r : LexTriple G} :
  r ∈ reps A B C s ↔
    (ofLexTriple r).1 ∈ A ∧ (ofLexTriple r).2.1 ∈ B ∧
      (ofLexTriple r).2.2 ∈ C ∧
        (ofLexTriple r).1 + (ofLexTriple r).2.1 + (ofLexTriple r).2.2 = s := by
  constructor
  · intro hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨hx, hsum⟩ := Finset.mem_filter.1 hx
    obtain ⟨ha, hbc⟩ := Finset.mem_product.1 hx
    obtain ⟨hb, hc⟩ := Finset.mem_product.1 hbc
    exact ⟨ha, hb, hc, hsum⟩
  · intro hr
    refine Finset.mem_image.2 ⟨ofLexTriple r, ?_, toLexTriple_ofLexTriple r⟩
    exact Finset.mem_filter.2 ⟨Finset.mem_product.2
      ⟨hr.1, Finset.mem_product.2 ⟨hr.2.1, hr.2.2.1⟩⟩, hr.2.2.2⟩

end MetaMathlibExt

namespace MetaMathlibExt

/--
[canonicalRep_mem](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean)
-/
@[path]
private lemma canonicalRep_mem {G : Type*} [DecidableEq G] [AddSemigroup G]
  [LinearOrder G] [Inhabited G] {A B C : Finset G} {s : G} (hs : s ∈ A + B + C) :
  canonicalRep A B C s ∈ reps A B C s := by
  simp only [canonicalRep, dite_eq_left hs]
  exact Finset.min'_mem _ _

end MetaMathlibExt

namespace MetaMathlibExt

/--
[canonicalRep_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean)
-/
@[path]
private lemma canonicalRep_le {G : Type*} [DecidableEq G] [AddSemigroup G]
  [LinearOrder G] [Inhabited G] {A B C : Finset G} {s : G} (hs : s ∈ A + B + C)
  {r : LexTriple G} (hr : r ∈ reps A B C s) : canonicalRep A B C s ≤ r := by
  simp only [canonicalRep, dite_eq_left hs]
  exact Finset.min'_le _ _ hr

end MetaMathlibExt

namespace MetaMathlibExt

/--
[card_sq_le_card_projections](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean)
-/
@[path]
private lemma card_sq_le_card_projections
  {α β γ : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
  (S : Finset (α × (β × γ))) :
  S.card ^ 2 ≤
    (S.image fun x => (x.1, x.2.1)).card *
      (S.image fun x => x.2).card *
        (S.image fun x => (x.1, x.2.2)).card := by
  let X := S.image fun x => x.1
  let P12 := S.image fun x => (x.1, x.2.1)
  let P23 := S.image fun x => x.2
  let P13 := S.image fun x => (x.1, x.2.2)
  let R (a : α) := S.filter fun x => x.1 = a
  let F12 (a : α) := P12.filter fun x => x.1 = a
  let F13 (a : α) := P13.filter fun x => x.1 = a
  have hR (a : α) : (R a).card ≤ (F12 a).card * (F13 a).card := by
    rw [← Finset.card_product]
    apply Finset.card_le_card_of_injOn
      (fun x : α × (β × γ) => ((x.1, x.2.1), (x.1, x.2.2)))
    · intro x hx
      have hxS : x ∈ S := (Finset.mem_filter.1 hx).1
      have hxa : x.1 = a := (Finset.mem_filter.1 hx).2
      rw [Finset.mem_coe, Finset.mem_product]
      constructor
      · exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨x, hxS, rfl⟩, hxa⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨x, hxS, rfl⟩, hxa⟩
    · intro x hx y hy hxy
      exact Prod.ext (congrArg (fun z => z.1.1) hxy)
        (Prod.ext (congrArg (fun z => z.1.2) hxy) (congrArg (fun z => z.2.2) hxy))
  have hD (a : α) : (R a).card ≤ P23.card := by
    apply Finset.card_le_card_of_injOn (fun x => x.2)
    · intro x hx
      simp only [Finset.mem_coe]
      exact Finset.mem_image.2 ⟨x, (Finset.mem_filter.1 hx).1, rfl⟩
    · intro x hx y hy hxy
      apply Prod.ext
      · exact (Finset.mem_filter.1 hx).2.trans (Finset.mem_filter.1 hy).2.symm
      · exact hxy
  have hlocal (a : α) (_ha : a ∈ X) :
    (R a).card ^ 2 ≤ (F12 a).card * (P23.card * (F13 a).card) := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      Nat.mul_le_mul (hR a) (hD a)
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul X
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _) hlocal
  have hS : S.card = ∑ a ∈ X, (R a).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    exact Finset.mem_image.2 ⟨x, hx, rfl⟩
  have h12 : P12.card = ∑ a ∈ X, (F12 a).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_image.2 ⟨y, hy, rfl⟩
  have h13 : P13.card = ∑ a ∈ X, (F13 a).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    exact Finset.mem_image.2 ⟨y, hy, rfl⟩
  rw [← hS, ← h12, ← Finset.mul_sum, ← h13] at hcs
  simpa [P12, P23, P13, mul_assoc] using hcs

end MetaMathlibExt

namespace MetaMathlibExt

/--
[three_sumset_card_sq_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean)
-/
@[path]
private lemma three_sumset_card_sq_le {G : Type*} [AddCommGroup G] [LinearOrder G]
  [DecidableEq G] [Inhabited G] (A B C : Finset G) :
  ((A + B + C).card : ℕ) ^ 2 ≤ (A + B).card * (B + C).card * (C + A).card := by
  let T := A + B + C
  let f (s : G) := ofLexTriple (canonicalRep A B C s)
  let S := T.image f
  have hf (s : G) (hs : s ∈ T) :
    (f s).1 ∈ A ∧ (f s).2.1 ∈ B ∧ (f s).2.2 ∈ C ∧
      (f s).1 + (f s).2.1 + (f s).2.2 = s := by
    exact mem_reps_iff.1 (canonicalRep_mem (by simpa [T] using hs))
  have hcard : S.card = T.card := by
    apply (Finset.card_image_iff.mpr ?_)
    intro s hs t ht hst
    have hs' := (hf s hs).2.2.2
    have ht' := (hf t ht).2.2.2
    rw [hst] at hs'
    exact hs'.symm.trans ht'
  have h12 : (S.image fun x => (x.1, x.2.1)).card ≤ (A + B).card := by
    apply Finset.card_le_card_of_injOn (fun x => x.1 + x.2)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_add.2 ⟨_, (hf s hs).1, _, (hf s hs).2.1, rfl⟩
    · intro x hx y hy hxy
      obtain ⟨xs, hxs, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨ys, hys, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hxs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hys
      have hfs := hf s hs
      have hft := hf t ht
      change (f s).1 + (f s).2.1 = (f t).1 + (f t).2.1 at hxy
      let altS := toLexTriple ((f t).1, ((f t).2.1, (f s).2.2))
      let altT := toLexTriple ((f s).1, ((f s).2.1, (f t).2.2))
      have haltS : altS ∈ reps A B C s := by
        apply mem_reps_iff.2
        simp only [altS, ofLexTriple_toLexTriple]
        refine ⟨hft.1, hft.2.1, hfs.2.2.1, ?_⟩
        exact (congrArg (· + (f s).2.2) hxy.symm).trans hfs.2.2.2
      have haltT : altT ∈ reps A B C t := by
        apply mem_reps_iff.2
        simp only [altT, ofLexTriple_toLexTriple]
        refine ⟨hfs.1, hfs.2.1, hft.2.2.1, ?_⟩
        exact (congrArg (· + (f t).2.2) hxy).trans hft.2.2.2
      have hleS := canonicalRep_le (by simpa [T] using hs) haltS
      have hleT := canonicalRep_le (by simpa [T] using ht) haltT
      have hcanS : toLexTriple (f s) = canonicalRep A B C s := by simp [f]
      have hcanT : toLexTriple (f t) = canonicalRep A B C t := by simp [f]
      rw [← hcanS] at hleS
      rw [← hcanT] at hleT
      have hpairs : toLex ((f s).1, (f s).2.1) ≤ toLex ((f t).1, (f t).2.1) := by
        simp only [toLexTriple, altS, Prod.Lex.toLex_le_toLex] at hleS ⊢
        obtain ha | ⟨ha, hbc⟩ := hleS
        · exact Or.inl ha
        · refine Or.inr ⟨ha, ?_⟩
          obtain hb | ⟨hb, _⟩ := hbc
          · exact hb.le
          · exact hb.le
      have hpairt : toLex ((f t).1, (f t).2.1) ≤ toLex ((f s).1, (f s).2.1) := by
        simp only [toLexTriple, altT, Prod.Lex.toLex_le_toLex] at hleT ⊢
        obtain ha | ⟨ha, hbc⟩ := hleT
        · exact Or.inl ha
        · refine Or.inr ⟨ha, ?_⟩
          obtain hb | ⟨hb, _⟩ := hbc
          · exact hb.le
          · exact hb.le
      exact congrArg ofLex (le_antisymm hpairs hpairt)
  have h23 : (S.image fun x => x.2).card ≤ (B + C).card := by
    apply Finset.card_le_card_of_injOn (fun x => x.1 + x.2)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_add.2 ⟨_, (hf s hs).2.1, _, (hf s hs).2.2.1, rfl⟩
    · intro x hx y hy hxy
      obtain ⟨xs, hxs, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨ys, hys, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hxs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hys
      have hfs := hf s hs
      have hft := hf t ht
      change (f s).2.1 + (f s).2.2 = (f t).2.1 + (f t).2.2 at hxy
      let altS := toLexTriple ((f s).1, ((f t).2.1, (f t).2.2))
      let altT := toLexTriple ((f t).1, ((f s).2.1, (f s).2.2))
      have haltS : altS ∈ reps A B C s := by
        apply mem_reps_iff.2
        simp only [altS, ofLexTriple_toLexTriple]
        refine ⟨hfs.1, hft.2.1, hft.2.2.1, ?_⟩
        calc
          (f s).1 + (f t).2.1 + (f t).2.2 =
            (f s).1 + ((f t).2.1 + (f t).2.2) := add_assoc _ _ _
          _ = (f s).1 + ((f s).2.1 + (f s).2.2) :=
            congrArg ((f s).1 + ·) hxy.symm
          _ = (f s).1 + (f s).2.1 + (f s).2.2 := (add_assoc _ _ _).symm
          _ = s := hfs.2.2.2
      have haltT : altT ∈ reps A B C t := by
        apply mem_reps_iff.2
        simp only [altT, ofLexTriple_toLexTriple]
        refine ⟨hft.1, hfs.2.1, hfs.2.2.1, ?_⟩
        calc
          (f t).1 + (f s).2.1 + (f s).2.2 =
            (f t).1 + ((f s).2.1 + (f s).2.2) := add_assoc _ _ _
          _ = (f t).1 + ((f t).2.1 + (f t).2.2) :=
            congrArg ((f t).1 + ·) hxy
          _ = (f t).1 + (f t).2.1 + (f t).2.2 := (add_assoc _ _ _).symm
          _ = t := hft.2.2.2
      have hleS := canonicalRep_le (by simpa [T] using hs) haltS
      have hleT := canonicalRep_le (by simpa [T] using ht) haltT
      have hcanS : toLexTriple (f s) = canonicalRep A B C s := by simp [f]
      have hcanT : toLexTriple (f t) = canonicalRep A B C t := by simp [f]
      rw [← hcanS] at hleS
      rw [← hcanT] at hleT
      have hpairs : toLex ((f s).2.1, (f s).2.2) ≤
        toLex ((f t).2.1, (f t).2.2) := by
        simp only [toLexTriple, altS, Prod.Lex.toLex_le_toLex] at hleS
        obtain hbad | ⟨_, hgood⟩ := hleS
        · exact (lt_irrefl _ hbad).elim
        · exact Prod.Lex.toLex_le_toLex.2 hgood
      have hpairt : toLex ((f t).2.1, (f t).2.2) ≤
        toLex ((f s).2.1, (f s).2.2) := by
        simp only [toLexTriple, altT, Prod.Lex.toLex_le_toLex] at hleT
        obtain hbad | ⟨_, hgood⟩ := hleT
        · exact (lt_irrefl _ hbad).elim
        · exact Prod.Lex.toLex_le_toLex.2 hgood
      exact congrArg ofLex (le_antisymm hpairs hpairt)
  have h13 : (S.image fun x => (x.1, x.2.2)).card ≤ (C + A).card := by
    apply Finset.card_le_card_of_injOn (fun x => x.2 + x.1)
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hy
      exact Finset.mem_add.2 ⟨_, (hf s hs).2.2.1, _, (hf s hs).1, rfl⟩
    · intro x hx y hy hxy
      obtain ⟨xs, hxs, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨ys, hys, rfl⟩ := Finset.mem_image.1 hy
      obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 hxs
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hys
      have hfs := hf s hs
      have hft := hf t ht
      change (f s).2.2 + (f s).1 = (f t).2.2 + (f t).1 at hxy
      have hac : (f s).1 + (f s).2.2 = (f t).1 + (f t).2.2 := by
        simpa [add_comm] using hxy
      let altS := toLexTriple ((f t).1, ((f s).2.1, (f t).2.2))
      let altT := toLexTriple ((f s).1, ((f t).2.1, (f s).2.2))
      have haltS : altS ∈ reps A B C s := by
        apply mem_reps_iff.2
        simp only [altS, ofLexTriple_toLexTriple]
        refine ⟨hft.1, hfs.2.1, hft.2.2.1, ?_⟩
        calc
          (f t).1 + (f s).2.1 + (f t).2.2 =
            ((f t).1 + (f t).2.2) + (f s).2.1 := by ac_rfl
          _ = ((f s).1 + (f s).2.2) + (f s).2.1 :=
            congrArg (· + (f s).2.1) hac.symm
          _ = (f s).1 + (f s).2.1 + (f s).2.2 := by ac_rfl
          _ = s := hfs.2.2.2
      have haltT : altT ∈ reps A B C t := by
        apply mem_reps_iff.2
        simp only [altT, ofLexTriple_toLexTriple]
        refine ⟨hfs.1, hft.2.1, hfs.2.2.1, ?_⟩
        calc
          (f s).1 + (f t).2.1 + (f s).2.2 =
            ((f s).1 + (f s).2.2) + (f t).2.1 := by ac_rfl
          _ = ((f t).1 + (f t).2.2) + (f t).2.1 :=
            congrArg (· + (f t).2.1) hac
          _ = (f t).1 + (f t).2.1 + (f t).2.2 := by ac_rfl
          _ = t := hft.2.2.2
      have hleS := canonicalRep_le (by simpa [T] using hs) haltS
      have hleT := canonicalRep_le (by simpa [T] using ht) haltT
      have hcanS : toLexTriple (f s) = canonicalRep A B C s := by simp [f]
      have hcanT : toLexTriple (f t) = canonicalRep A B C t := by simp [f]
      rw [← hcanS] at hleS
      rw [← hcanT] at hleT
      have ha : (f s).1 ≤ (f t).1 := by
        simp only [toLexTriple, altS, Prod.Lex.toLex_le_toLex] at hleS
        obtain ha | ⟨ha, _⟩ := hleS
        · exact ha.le
        · exact ha.le
      have hat : (f t).1 ≤ (f s).1 := by
        simp only [toLexTriple, altT, Prod.Lex.toLex_le_toLex] at hleT
        obtain ha | ⟨ha, _⟩ := hleT
        · exact ha.le
        · exact ha.le
      have haeq : (f s).1 = (f t).1 := le_antisymm ha hat
      rw [haeq] at hac
      rw [haeq, add_left_cancel hac]
  have hproj := card_sq_le_card_projections S
  calc
    T.card ^ 2 = S.card ^ 2 := by rw [hcard]
    _ ≤ (S.image fun x => (x.1, x.2.1)).card *
      (S.image fun x => x.2).card * (S.image fun x => (x.1, x.2.2)).card := hproj
    _ ≤ (A + B).card * (B + C).card * (C + A).card :=
      Nat.mul_le_mul (Nat.mul_le_mul h12 h23) h13
    _ = (A + B).card * (B + C).card * (C + A).card := rfl

end MetaMathlibExt

namespace MetaMathlibExt

/--
[gyarmatiMatolcsiRuzsa_three_sumset_zmod_aux](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean)
-/
@[path]
private lemma gyarmatiMatolcsiRuzsa_three_sumset_zmod_aux (p : ℕ) (hp : Nat.Prime p)
  (_hodd : Odd p) (A B C : Finset (ZMod p)) :
  ((A + B + C).card : ℕ) ^ 2 ≤ (A + B).card * (B + C).card * (C + A).card := by
  let ABC := A + B + C
  let AB := A + B
  let BC := B + C
  let CA := C + A
  change ABC.card ^ 2 ≤ AB.card * BC.card * CA.card
  let _ : NeZero p := ⟨hp.ne_zero⟩
  let oldDecEq : DecidableEq (ZMod p) := inferInstance
  let ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin (ZMod p)
  let _ : LinearOrder (ZMod p) := LinearOrder.lift' e e.injective
  let _ : DecidableEq (ZMod p) := oldDecEq
  exact three_sumset_card_sq_le A B C

end MetaMathlibExt

namespace MetaMathlibExt

/--
[gyarmatiMatolcsiRuzsa_three_sumset_zmod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Additive/ThreeSumset.lean)
-/
@[path]
lemma gyarmatiMatolcsiRuzsa_three_sumset_zmod
  {p : ℕ}
  {A B C : Finset (ZMod p)}
-- given
  (hp : Nat.Prime p)
  (hodd : Odd p) :
-- imply
  ((A + B + C).card : ℕ) ^ 2 ≤ (A + B).card * (B + C).card * (C + A).card :=
-- proof
  gyarmatiMatolcsiRuzsa_three_sumset_zmod_aux p hp hodd A B C

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
