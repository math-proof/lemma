/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticDirichletCharacter.lean -/

import sympy.atlas.NumberTheory.DirichletCharacter.Quadratic
import Lemma.Nat.DirichletCharacter.Quadratic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lemma.Nat.DirichletCharacter.KroneckerJacobiOdd
section
namespace MetaMathlibExt

private noncomputable def mkChar (N : ℕ) (hN : N ≠ 0) (F : ℕ → ℤ)
    (h1 : F 1 = 1)
    (hmul : ∀ m n : ℕ, F (m * n) = F m * F n)
    (hper : ∀ a b : ℕ, (a : ZMod N) = (b : ZMod N) → F a = F b)
    (hzero : ∀ a : ZMod N, ¬IsUnit a → F a.val = 0) :
    MulChar (ZMod N) ℤ where
  toFun a := F a.val
  map_one' := by
    have : NeZero N := ⟨hN⟩
    change F (1 : ZMod N).val = 1
    have h : F (1 : ZMod N).val = F 1 := hper _ _ (by simp)
    rw [h, h1]
  map_mul' := by
    have : NeZero N := ⟨hN⟩
    intro a b
    change F (a * b).val = F a.val * F b.val
    have hcast : ((a.val * b.val : ℕ) : ZMod N) = a * b := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have hper' : F (a * b).val = F (a.val * b.val) :=
      hper _ _ (by rw [ZMod.natCast_zmod_val, hcast])
    rw [hper', hmul]
  map_nonunit' := by
    intro a ha
    exact hzero a ha
end MetaMathlibExt
end
