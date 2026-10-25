import Mathlib
import Def.Analysis.Misc.erdos_707


lemma IsPerfectDifferenceSet.card {N: ℕ} [NeZero N] {B: Finset (ZMod N)} (hdiff: IsPerfectDifferenceSet B) : B.card * B.card + 1 = N + B.card := by
  have he : Function.Bijective (IsPerfectDifferenceSet.map B) := by
    constructor
    . intro p p' hpp'
      rcases p with ⟨ x,y ⟩ | _ <;> rcases p' with ⟨ x',y' ⟩ | _ <;> simp_all [IsPerfectDifferenceSet.map]
      . by_cases hxy : x = y <;> by_cases hx'y' : x' = y' <;> simp_all
        have := (hdiff (x.val - y.val) (by grind)).unique (y₁ := ⟨ x,y ⟩) (y₂ := ⟨ x',y' ⟩)
        grind
      . by_cases hxy : x = y <;> grind
      by_cases hxy' : x' = y' <;> grind
    rintro (x | b)
    . by_cases h : x = 0
      . use Sum.inr Unit.unit
        simp [IsPerfectDifferenceSet.map, h]
      have := (hdiff x h).exists.choose_spec
      set b := (hdiff x h).exists.choose
      use Sum.inl b
      have hb : b.1 ≠ b.2 := by grind
      simp [IsPerfectDifferenceSet.map, hb, this]
    use Sum.inl ⟨ b, b ⟩
    simp [IsPerfectDifferenceSet.map]
  replace he := Fintype.card_of_bijective he
  simp [Fintype.card_sum] at he
  convert he

