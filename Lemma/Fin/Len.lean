import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.GeometricAlgebra.OppositeConjugacyProof
open GeometricAlgebra


/--
[isOppositeFlag_sup_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyProof.lean)
-/
@[path]
private lemma main
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F F' : Flag k V}
  {i : Fin F.len}
-- given
  (h : Flag.isOppositeFlag F F') :
-- imply
  let j : Fin F'.len := ⟨F'.len - 1 - i.val, by have := h.1; omega⟩ F.spaces i ⊔ F'.spaces j = ⊤ := by
-- proof
  obtain ⟨hlen, _, hcompl⟩ := h
  exact (hcompl hlen i).1



/--
[isOppositeFlag_inf_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyProof.lean)
-/
private lemma isOppositeFlag_inf_eq_bot
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F F' : Flag k V}
  {i : Fin F.len}
-- given
  (h : Flag.isOppositeFlag F F') :
-- imply
  let j : Fin F'.len := ⟨F'.len - 1 - i.val, by have := h.1; omega⟩ F.spaces i ⊓ F'.spaces j = ⊥ := by
-- proof
  obtain ⟨hlen, _, hcompl⟩ := h
  exact (hcompl hlen i).2


/--
[opposite_flags_same_len](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/GeometricAlgebra/OppositeConjugacyProof.lean)
-/
private lemma opposite_flags_same_len_eq
  [Field k]
  [AddCommGroup V]
  [Module k V]
  {F F'₁ F'₂ : Flag k V}
-- given
  (h₁ : Flag.isOppositeFlag F F'₁)
  (h₂ : Flag.isOppositeFlag F F'₂) :
-- imply
  F'₁.len = F'₂.len := by
-- proof
  apply GeometricAlgebra.opposite_flags_same_len F F'₁ F'₂ h₁ h₂


-- created on 2026-10-23
-- updated on 2026-10-24
