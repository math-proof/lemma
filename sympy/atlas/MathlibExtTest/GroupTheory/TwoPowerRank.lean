/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/TwoPowerRank.lean -/


import sympy.atlas.GroupTheory.TwoPowerRank
import Lemma.Int.LeTwoPowerImage
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.LinearAlgebra.Dimension.Finite


namespace AbelianGroupTest

example : AbelianGroup.twoPowerImage (ZMod 4) 0 = ⊤ := by
  ext x
  simp [AbelianGroup.twoPowerImage]

noncomputable example (j : ℕ) [Fact (0 < j)] :
    Module (ZMod 2) (AbelianGroup.higherTwoPowerLayer (ZMod 8) j) :=
  inferInstance

example :
    AbelianGroup.fourRank (ZMod 8) =
      letI : Fact (0 < 2) := ⟨by norm_num⟩
      Module.finrank (ZMod 2) (AbelianGroup.higherTwoPowerLayer (ZMod 8) 2) :=
  AbelianGroup.fourRank_eq (ZMod 8)

example : AbelianGroup.fourRank PUnit = 0 := by
  let _ : Fact (0 < 2) := ⟨by norm_num⟩
  change Module.finrank (ZMod 2) (AbelianGroup.higherTwoPowerLayer PUnit 2) = 0
  let _ : Subsingleton (AbelianGroup.higherTwoPowerLayer PUnit 2) := ⟨by
    intro x y
    induction x using QuotientAddGroup.induction_on
    induction y using QuotientAddGroup.induction_on
    rename_i x y
    have hxy : x = y := by
      apply Subtype.ext
      exact Subsingleton.elim _ _
    subst y
    rfl⟩
  exact Module.finrank_zero_of_subsingleton

set_option linter.style.haveILetI false in
example : 0 < AbelianGroup.higherTwoPowerRank (ZMod 2) 1 (by norm_num) := by
  have hH : AbelianGroup.twoPowerImage (ZMod 2) 0 = ⊤ := by
    ext x
    simp [AbelianGroup.twoPowerImage]
  have hK : AbelianGroup.twoPowerImage (ZMod 2) 1 = ⊥ := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      change (2 : ℤ) • y = 0
      simpa [Nat.cast_smul_eq_nsmul] using (ZModModule.char_nsmul_eq_zero 2 y)
    · intro hx
      rw [Submodule.mem_bot] at hx
      subst x
      exact ⟨0, by simp⟩
  letI : Fact (0 < 1) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : NeZero 2 := ⟨by norm_num⟩
  rw [AbelianGroup.higherTwoPowerRank_eq]
  rw [Module.finrank_pos_iff_exists_ne_zero]
  let x : AbelianGroup.twoPowerImage (ZMod 2) 0 := ⟨1, by rw [hH]; simp⟩
  refine ⟨QuotientAddGroup.mk' _ x, ?_⟩
  intro hx
  have hxmem := (QuotientAddGroup.eq_zero_iff x).mp hx
  change (x : ZMod 2) ∈ AbelianGroup.twoPowerImage (ZMod 2) 1 at hxmem
  rw [hK] at hxmem
  simp [x] at hxmem

example (j : ℕ) (hj : 0 < j) :
    AbelianGroup.higherTwoPowerRank (ZMod 8) j hj =
      letI : Fact (0 < j) := ⟨hj⟩
      Module.finrank (ZMod 2) (AbelianGroup.higherTwoPowerLayer (ZMod 8) j) :=
  AbelianGroup.higherTwoPowerRank_eq (ZMod 8) j hj

end AbelianGroupTest
