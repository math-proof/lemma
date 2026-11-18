module

public import Mathlib
public import Theorem.Analysis.Section_5_2.Part2
public import Mathlib.Algebra.Group.MinimalAxioms
public import Instance.Analysis.Section_5_3.Part5

public section
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

/-- Constant sequences are Cauchy. Private helper only. -/
private theorem isCauchy_ofNatFun_const (q : ℚ) :
    (Sequence.ofNatFun (fun _ ↦ q)).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  intro ε hε
  refine ⟨0, ?_⟩
  intro j _ k _
  rw [Section_4_3.dist_eq]
  simpa using le_of_lt hε

public theorem Real.ratCast_def (q:ℚ) : (q:Real) = LIM (fun _ ↦ q) := by
  rw [LIM_def (isCauchy_ofNatFun_const q)]
  rfl

/-- Proposition 5.3.11 (laws of algebra): associativity, first `AddGroup.ofLeftAxioms` law. -/
public theorem Real.add_assoc (a b c : Real) : a + b + c = a + (b + c) := by
  obtain ⟨A, hA, rfl⟩ := eq_lim a
  obtain ⟨B, hB, rfl⟩ := eq_lim b
  obtain ⟨C, hC, rfl⟩ := eq_lim c
  have hAB := Sequence.IsCauchy.add hA hB
  have hBC := Sequence.IsCauchy.add hB hC
  rw [LIM_add hA hB, LIM_add hAB hC, LIM_add hB hC, LIM_add hA hBC]
  have hfun : (A + B) + C = A + (B + C) := by
    ext n
    simp [Pi.add_apply]
    exact _root_.add_assoc (A n) (B n) (C n)
  rw [hfun]

/-- Proposition 5.3.11 (laws of algebra): left identity, second `AddGroup.ofLeftAxioms` law.
    Stated with `RatCast` (available in this module) so it is definitionally `0 + a = a`
    once `Real.instOfNat` lands in Instance.Part6; avoids a cycle with Instance.Part7. -/
public theorem Real.zero_add (a : Real) : ((0 : ℚ) : Real) + a = a := by
  obtain ⟨A, hA, rfl⟩ := eq_lim a
  rw [ratCast_def, LIM_add (isCauchy_ofNatFun_const 0) hA]
  have hfun : (fun _ ↦ (0 : ℚ)) + A = A := by
    ext n
    simp [Pi.add_apply]
  rw [hfun]

/-- Proposition 5.3.11 (laws of algebra): left inverse, third `AddGroup.ofLeftAxioms` law.
    Stated with `RatCast` and `Mul` (the definition of `Real.instNeg`) so it is definitionally
    `-a + a = 0` once `Real.instNeg` lands in Instance.Part7; avoids a cycle. -/
public theorem Real.neg_add_cancel (a : Real) :
    ((-1 : ℚ) : Real) * a + a = ((0 : ℚ) : Real) := by
  obtain ⟨A, hA, rfl⟩ := eq_lim a
  have hneg1 := isCauchy_ofNatFun_const (-1)
  have hnegA := Sequence.IsCauchy.mul hneg1 hA
  rw [ratCast_def, ratCast_def, LIM_mul hneg1 hA, LIM_add hnegA hA]
  have hfun : (fun _ ↦ (-1 : ℚ)) * A + A = fun _ ↦ (0 : ℚ) := by
    ext n
    simp [Pi.add_apply, Pi.mul_apply]
  rw [hfun]

/-- Proposition 5.3.11 (laws of algebra): multiplicative associativity, `CommMonoid.mul_assoc`. -/
public theorem Real.mul_assoc (a b c : Real) : a * b * c = a * (b * c) := by
  obtain ⟨A, hA, rfl⟩ := eq_lim a
  obtain ⟨B, hB, rfl⟩ := eq_lim b
  obtain ⟨C, hC, rfl⟩ := eq_lim c
  have hAB := Sequence.IsCauchy.mul hA hB
  have hBC := Sequence.IsCauchy.mul hB hC
  rw [LIM_mul hA hB, LIM_mul hAB hC, LIM_mul hB hC, LIM_mul hA hBC]
  have hfun : (A * B) * C = A * (B * C) := by
    ext n
    simp [Pi.mul_apply]
    exact _root_.mul_assoc (A n) (B n) (C n)
  rw [hfun]

/-- Proposition 5.3.11 (laws of algebra): left unit, `CommMonoid.one_mul`.
    Stated with `RatCast` so it is definitionally `1 * a = a` once `Real.instOfNat` lands. -/
public theorem Real.one_mul (a : Real) : ((1 : ℚ) : Real) * a = a := by
  obtain ⟨A, hA, rfl⟩ := eq_lim a
  rw [ratCast_def, LIM_mul (isCauchy_ofNatFun_const 1) hA]
  have hfun : (fun _ ↦ (1 : ℚ)) * A = A := by
    ext n
    simp [Pi.mul_apply]
  rw [hfun]

/-- Proposition 5.3.11 (laws of algebra): right unit, `CommMonoid.mul_one`.
    Stated with `RatCast` so it is definitionally `a * 1 = a` once `Real.instOfNat` lands. -/
public theorem Real.mul_one (a : Real) : a * ((1 : ℚ) : Real) = a := by
  obtain ⟨A, hA, rfl⟩ := eq_lim a
  rw [ratCast_def, LIM_mul hA (isCauchy_ofNatFun_const 1)]
  have hfun : A * (fun _ ↦ (1 : ℚ)) = A := by
    ext n
    simp [Pi.mul_apply]
  rw [hfun]

/-- Proposition 5.3.11 (laws of algebra): commutativity, `CommMonoid.mul_comm`. -/
public theorem Real.mul_comm (a b : Real) : a * b = b * a := by
  obtain ⟨A, hA, rfl⟩ := eq_lim a
  obtain ⟨B, hB, rfl⟩ := eq_lim b
  rw [LIM_mul hA hB, LIM_mul hB hA]
  have hfun : A * B = B * A := by
    ext n
    simp [Pi.mul_apply]
    exact _root_.mul_comm (A n) (B n)
  rw [hfun]

end Chapter5
