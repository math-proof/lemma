import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Combinatorics.JaccardLattice
open JaccardLattice


namespace JaccardLatticeTest

/--
[countVal_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma countVal_pos : IsStrictlyPositive countVal := by
  intro X
  unfold countVal
  have hnn : (0 : ℝ) ≤ ((X : ℕ) : ℝ) := Nat.cast_nonneg X
  linarith

end JaccardLatticeTest

namespace JaccardLatticeTest

/--
[countVal_mono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma countVal_mono : Monotone countVal := by
  intro X Y hXY
  unfold countVal
  have hc : ((X : ℕ) : ℝ) ≤ ((Y : ℕ) : ℝ) := Nat.cast_le.mpr hXY
  linarith

end JaccardLatticeTest

namespace JaccardLatticeTest

/--
[countVal_mod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma countVal_mod : IsModularValuation countVal := by
  intro X Y
  obtain h | h := le_total X Y
  · have hSup : X ⊔ Y = Y := le_antisymm (sup_le h le_rfl) le_sup_right
    have hInf : X ⊓ Y = X := le_antisymm inf_le_left (le_inf le_rfl h)
    rw [hSup, hInf]
    exact add_comm _ _
  · have hSup : X ⊔ Y = X := le_antisymm (sup_le le_rfl h) le_sup_left
    have hInf : X ⊓ Y = Y := le_antisymm inf_le_right (le_inf h le_rfl)
    rw [hSup, hInf]

end JaccardLatticeTest

namespace JaccardLatticeTest

/--
[countVal_01](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma countVal_01 : jaccardDist countVal 0 1 = 1 / 2 := by
  have hi : (0 : ℕ) ⊓ 1 = 0 :=
    le_antisymm inf_le_left (le_inf le_rfl (Nat.zero_le 1))
  have hs : (0 : ℕ) ⊔ 1 = 1 :=
    le_antisymm (sup_le (Nat.zero_le 1) le_rfl) le_sup_right
  unfold jaccardDist
  rw [hi, hs]
  norm_num [countVal]

end JaccardLatticeTest

namespace JaccardLatticeTest

/--
[countVal_12](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma countVal_12 : jaccardDist countVal 1 2 = 1 / 3 := by
  have hle : (1 : ℕ) ≤ 2 := by decide
  have hi : (1 : ℕ) ⊓ 2 = 1 := le_antisymm inf_le_left (le_inf le_rfl hle)
  have hs : (1 : ℕ) ⊔ 2 = 2 := le_antisymm (sup_le hle le_rfl) le_sup_right
  unfold jaccardDist
  rw [hi, hs]
  norm_num [countVal]

end JaccardLatticeTest

namespace JaccardLatticeTest

/--
[countVal_02](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/JaccardLattice.lean)
-/
@[path]
private lemma countVal_02 : jaccardDist countVal 0 2 = 2 / 3 := by
  have hi : (0 : ℕ) ⊓ 2 = 0 :=
    le_antisymm inf_le_left (le_inf le_rfl (Nat.zero_le 2))
  have hs : (0 : ℕ) ⊔ 2 = 2 :=
    le_antisymm (sup_le (Nat.zero_le 2) le_rfl) le_sup_right
  unfold jaccardDist
  rw [hi, hs]
  norm_num [countVal]

end JaccardLatticeTest


-- created on 2026-10-23
