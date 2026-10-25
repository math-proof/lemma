import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.PadicQpCompletion
open scoped Padic


/--
[padic_withValRingEquiv_ratEmbed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicQpCompletion.lean)
-/
@[path]
lemma padic_withValRingEquiv_ratEmbed
  {p : ℕ}
  [hp : Fact p.Prime]
  {q : ℚ} :
-- imply
  (Padic.withValRingEquiv (p := p)) (ratEmbedPadicCompletion p q) = (q : ℚ_[p]) := by
-- proof
  show (Padic.withValRingEquiv (p := p))
    (↑((WithVal.equiv (Rat.padicValuation p)).symm q) : (Rat.padicValuation p).Completion) =
    (q : ℚ_[p])
  have heq : ∀ x : (Rat.padicValuation p).Completion,
    Padic.withValUniformEquiv x = Padic.withValRingEquiv x := by
    intro x
    exact congr_fun (congrArg Equiv.toFun
      (Padic.toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv (p := p))) x
  rw [← heq, Padic.withValUniformEquiv_cast_apply]
  simp

/--
[thm_8_1_padic_completion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicQpCompletion.lean)
-/
@[path]
lemma thm_8_1_padic_completion
  {p : ℕ}
  [hp : Fact p.Prime] :
-- imply
  ∃ (π : (Rat.padicValuation p).Completion ≃+* ℚ_[p]), ∀ (q : ℚ), ‖π (ratEmbedPadicCompletion p q)‖ = padicNorm p q :=
-- proof
  ⟨Padic.withValRingEquiv, fun q => by
    rw [padic_withValRingEquiv_ratEmbed]; exact Padic.eq_padicNorm q⟩


-- created on 2026-10-23
