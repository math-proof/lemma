import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.BoutonNim
open MetaMathlibExt.BoutonNim


/--
[bouton_nim_p_positions](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/BoutonNim.lean)
-/
@[path]
private lemma bouton_nim_p_positions_eq
  {pos : List ℕ} :
-- imply
  (List.foldl Nat.xor 0 pos = 0 →
    ∀ (i : Fin pos.length) (y : ℕ), y < pos.get i →
    List.foldl Nat.xor 0 (pos.set i.val y) ≠ 0) ∧
    (List.foldl Nat.xor 0 pos ≠ 0 →
    ∃ (i : Fin pos.length) (y : ℕ), y < pos.get i ∧
    List.foldl Nat.xor 0 (pos.set i.val y) = 0) := by
-- proof
  apply MetaMathlibExt.BoutonNim.bouton_nim_p_positions pos


-- created on 2026-10-20
