import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.RothAuxiliary
import Def.NumberTheory.RothAuxiliary.Part3
open MathlibExt.NumberTheory.RothAuxiliary
open Polynomial


/--
[rothPowerCoord_eval₂](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/RothAuxiliary.lean)
-/
@[path]
private lemma main
  [CommRing R]
  (f : ℤ →+* R)
  (g : ℤ[X])
  (β : R)
  (n : ℕ)
-- given
  (hroot : eval₂ f β g = 0) :
-- imply
  eval₂ f β (rothPowerCoord g n) = β ^ n := by
-- proof
  induction n with
  | zero =>
    simp [rothPowerCoord]
  | succ n ih =>
    simp [rothPowerCoord, ih, hroot, pow_succ']


-- created on 2026-10-21
-- updated on 2026-11-13
