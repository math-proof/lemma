/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/DicksonPGL2Wild.lean -/


import sympy.atlas.GroupTheory.DicksonPGL2Wild
import Lemma.Fin.Card.eq.MulCardSubSquareCard1


namespace MathlibExtTest.GroupTheory.DicksonPGL2Wild

open MetaMathlibExt.Dickson

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩
local instance : Fact (2 < 3) := ⟨by decide⟩

-- The order and map-injectivity APIs specialize to a genuine finite-field extension.
example :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) (ZMod 5)) = 120 ∧
      Function.Injective (Matrix.ProjGenLinGroup.map (n := Fin 2)
        (algebraMap (ZMod 5) (GaloisField 5 2))) := by
  constructor
  · rw [card_projGenLinGroup_fin_two (ZMod 5)]
    norm_num
  · exact projGenLinGroup_map_injective _ (RingHom.injective _)

-- In characteristic three, the public element theorem turns divisibility into a power identity.
example (g : Matrix.ProjGenLinGroup (Fin 2) (ZMod 3))
    (hfinite : orderOf g ≠ 0) (hdiv : 3 ∣ orderOf g) :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 3)) = 12 ∧
      g ^ 3 = 1 := by
  constructor
  · rw [card_projectiveSpecialLinearGroup_fin_two 3 (ZMod 3) (by norm_num)]
    norm_num
  · have horder := orderOf_eq_char_of_char_dvd g hfinite hdiv
    calc
      g ^ 3 = g ^ orderOf g := congrArg (fun n : ℕ ↦ g ^ n) horder.symm
      _ = 1 := pow_orderOf_eq_one g

end MathlibExtTest.GroupTheory.DicksonPGL2Wild
