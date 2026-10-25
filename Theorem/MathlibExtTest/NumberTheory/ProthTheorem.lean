/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/ProthTheorem.lean -/


import Lemma.Nat.ProthTheorem
import Mathlib.Tactic.NormNum


namespace MetaMathlibExt

-- The Proth number 13 has witness 2.
example : Nat.Prime 13 := by
  apply (proth_theorem 3 2 13 ⟨1, by norm_num⟩ (by norm_num) (by norm_num)).2
  exact ⟨2, by decide⟩

-- The composite Proth number 9 has no witness.
example : ¬∃ a : ZMod 9, a ^ ((9 - 1) / 2) = -1 := by
  intro ha
  have hp : Nat.Prime 9 :=
    (proth_theorem 1 3 9 (by norm_num) (by norm_num) (by norm_num)).2 ha
  exact (by decide : ¬Nat.Prime 9) hp

end MetaMathlibExt
