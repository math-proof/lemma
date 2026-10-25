import Mathlib
import Theorem.Analysis.Section_5_2.Part2
import Mathlib.Algebra.Group.MinimalAxioms
import Instance.Analysis.Section_5_3.Part4
/-!
# Analysis I, Section 5.3: The construction of the real numbers

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Notion of a formal limit of a Cauchy sequence.
- Construction of a real number type `Chapter5.Real`.
- Basic arithmetic operations and properties.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter5

theorem Real.LIM_mul {a b:ℕ → ℚ} (ha: (a:Sequence).IsCauchy) (hb: (b:Sequence).IsCauchy) :
  LIM a * LIM b = LIM (a * b) := by
  change Real.mul_inst.mul (LIM a) (LIM b) = LIM (a * b)
  unfold Real.mul_inst
  dsimp only
  rw [LIM_def ha, LIM_def hb, Quotient.liftOn₂_mk]
  have hfun :
      ((fun n : ℕ ↦ (CauchySequence.mk' ha).seq (n : ℤ)) *
        fun n : ℕ ↦ (CauchySequence.mk' hb).seq (n : ℤ)) = a * b := by
    ext n
    simp [Sequence.eval_coe_at_int, Int.toNat_natCast]
  rw [hfun]

end Chapter5
