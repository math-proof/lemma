import Mathlib
import Def.Analysis.Appendix_B_1
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


namespace AppendixB

instance Digit.instZero : Zero Digit := ⟨0, by decide⟩

instance Digit.instOne : One Digit := ⟨1, by decide⟩

instance Digit.instTwo : OfNat Digit 2 := ⟨2, by decide⟩

instance Digit.instThree : OfNat Digit 3 := ⟨3, by decide⟩

instance Digit.instFour : OfNat Digit 4 := ⟨4, by decide⟩

instance Digit.instFive : OfNat Digit 5 := ⟨5, by decide⟩

instance Digit.instSix : OfNat Digit 6 := ⟨6, by decide⟩

instance Digit.instSeven : OfNat Digit 7 := ⟨7, by decide⟩

instance Digit.instEight : OfNat Digit 8 := ⟨8, by decide⟩

instance Digit.instNine : OfNat Digit 9 := ⟨9, by decide⟩

instance Digit.instFintype : Fintype Digit := Fin.fintype 10

instance Digit.instDecidableEq : DecidableEq Digit := instDecidableEqFin 10

instance Digit.instInhabited : Inhabited Digit := ⟨ 0 ⟩

end AppendixB
