import Mathlib
import Theorem.Analysis.Misc.erdos_707.Part4


namespace Mainstep

export Hypotheses (p hp N  hN B hdiff embed h_embed h_inj)

variable [Hypotheses]

noncomputable def b (x:B) := if hx: x.val = 2 then ⟨ 2, h2 ⟩ else (second_fixed hx).choose

noncomputable def d (x:B) := if hx: x.val = 2 then ⟨ 2, h2 ⟩ else g (two_mul_sub_one_notin hx) (second_fixed hx).choose

end Mainstep
