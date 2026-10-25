import Mathlib
import Def.Analysis.Misc.erdos_707.Part3


namespace Mainstep

export Hypotheses (p hp N  hN B hdiff embed h_embed h_inj)

variable [Hypotheses]

/-- If there is one fixed point, there is another. -/
lemma f_second_fixed {a:ZMod N} {ha: a ∉ B} {b:B} (hb: f ha b = b) : ∃ c:B, c ≠ b ∧ f ha c = c := by
  let action := z2_vact ha
  classical
  have := action.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup _ _
  simp only [ZMod.card] at this
  set N :=  Fintype.card (Quotient (action.orbitRel (ZMod 2) { x // x ∈ B }))
  set S := action.fixedBy { x // x ∈ B } 1
  replace := calc
    N * 2 = ∑ a, Fintype.card (action.fixedBy { x // x ∈ B } a) := this.symm
    _ = Fintype.card (action.fixedBy { x // x ∈ B } 0) + Fintype.card S := by
      exact Fin.sum_univ_two _
    _ = B.card + Fintype.card S := by simp
  replace : Even (Fintype.card S) := by
    apply (Nat.even_add.mp ?_).mp heven
    rw [←this]
    grind
  have hs : b ∈ S := by
    change (if (1: ZMod 2) = 1 then f ha b else b) = b
    simp [hb]
  have c1 : Fintype.card S ≥ 1 := by
    haveI : Nonempty ↑S := ⟨⟨b, hs⟩⟩
    exact Fintype.card_pos
  replace c1 : Fintype.card S ≥ 2 := by grind
  have c2 : S ≠ {b} := by
    contrapose! c1
    simp [c1]
  have c3 : ∃ c:B, c ∈ S ∧ c ≠ b := by
    simp at c2
    grind
  obtain ⟨ c, hc ⟩ := c3
  use c; simp [hc]
  simp [S] at hc
  replace hc := hc.1
  change (if (1: ZMod 2) = 1 then f ha c else c) = c at hc
  simp_all

lemma two_mul_sub_one_notin {x:B} (hx: x.val ≠ 2) : 2 * (x.val - 1) ∉ B := by
  by_contra! this
  replace := diff_uniq (a:= x) (b := ⟨ 2,h2 ⟩) (c := ⟨_,this⟩) (d:=x) (by grind) (by grind)
  grind

lemma first_fixed {x:B} (hx: x.val ≠ 2) : f (two_mul_sub_one_notin hx) x = x := by
  convert ((f_def' (two_mul_sub_one_notin hx) x x ⟨ 2, h2⟩).mp ?_).1.symm
  grind

lemma second_fixed {x:B} (hx: x.val ≠ 2) : ∃ b, b ≠ x ∧ f (two_mul_sub_one_notin hx) b = b :=  f_second_fixed (first_fixed hx)

end Mainstep
