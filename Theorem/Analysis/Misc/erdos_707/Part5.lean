import Mathlib
import Def.Analysis.Misc.erdos_707.Part4


namespace Mainstep

export Hypotheses (p hp N  hN B hdiff embed h_embed h_inj)

variable [Hypotheses]

lemma b_neq {x:B} (hx: x.val ≠ 2) : b x ≠ x := by
  simp [b, hx]
  convert (second_fixed hx).choose_spec.1

lemma bd_ident (x:B) : 2 * (b x).val = 2 * (x.val - 1) + (d x).val := by
  by_cases hx: x.val = 2
  · simp [b,d,hx]; ring
  · simp [b, d, hx]
    convert f_fixed _ using 2
    convert (second_fixed hx).choose_spec.2

lemma d_injective : Function.Injective d := by
  intro x x' h
  have h1 := bd_ident x
  have h2 := bd_ident x'
  have h3 : 2 * ((b x).val - b x') = 2 * (x - x') := by grind
  replace h3 := (mul_two_inj h3).symm
  by_contra! this
  replace h3 := diff_uniq this h3
  have h4 := b_neq (x := x)
  have h5 := b_neq (x := x')
  grind

lemma d_surjective : Function.Surjective d := Finite.surjective_of_injective d_injective

lemma d1_eq_4 : d ⟨ 1, h1 ⟩ = ⟨ 4, h4 ⟩ := by
  obtain ⟨ x, hx ⟩ := d_surjective ⟨ 4, h4 ⟩
  have := bd_ident x
  simp [hx] at this
  replace : 2 * (b x).val = 2 * (x.val + 1) := by grind
  replace := mul_two_inj this
  convert hx
  convert congrArg Subtype.val (diff_uniq ?_ ?_ (a := ⟨ 2, h2 ⟩) (b := ⟨ 1, h1 ⟩) (c := b x) (d := x)).2
  . simp; convert h2_ne_1
  grind

lemma d1_eq_8 : d ⟨ 1, h1 ⟩ = ⟨ 8, h8 ⟩ := by
  obtain ⟨ x, hx ⟩ := d_surjective ⟨ 8, h8 ⟩
  have := bd_ident x
  simp [hx] at this
  replace : 2 * (b x).val = 2 * (x.val + 3) := by grind
  replace := mul_two_inj this
  convert hx
  convert congrArg Subtype.val (diff_uniq ?_ ?_ (a := ⟨ 4, h4 ⟩) (b := ⟨ 1, h1 ⟩) (c := b x) (d := x)).2
  . simp; convert h4_ne_1
  grind

lemma contradiction : False := by
  have := d1_eq_8
  rw [d1_eq_4] at this
  simp at this
  exact h4_ne_8 this

end Mainstep
