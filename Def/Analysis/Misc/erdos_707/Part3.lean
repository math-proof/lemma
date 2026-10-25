import Mathlib
import Theorem.Analysis.Misc.erdos_707.Part3


namespace Mainstep

export Hypotheses (p hp N  hN B hdiff embed h_embed h_inj)

variable [Hypotheses]

@[implicit_reducible] noncomputable def z2_vact {a:ZMod N} (ha: a ∉ B) : AddAction (ZMod 2) B :=
{
  vadd i b := if i=1 then f ha b else b
  zero_vadd b := by
    change (if (0: ZMod 2) = 1 then f ha b else b) = b
    simp
  add_vadd i j b := by
    change (if i + j = 1 then f ha b else b) = if i = 1 then f ha (if j = 1 then f ha b else b) else (if j = 1 then f ha b else b)
    fin_cases i <;> fin_cases j <;> dsimp only <;> first | rfl | exact (f_inv ha b).symm
}

end Mainstep
