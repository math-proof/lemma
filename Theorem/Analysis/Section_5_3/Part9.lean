module

public import Mathlib
public import Theorem.Analysis.Section_5_2.Part2
public import Mathlib.Algebra.Group.MinimalAxioms
public import Instance.Analysis.Section_5_3.Part7

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

public theorem Real.sub_eq_add_neg (x y:Real) : x - y = x + (-y) := rfl

/-- Every constant sequence is Cauchy. -/
public theorem Sequence.IsCauchy.const (a:ℚ) : (Sequence.ofNatFun (fun _ ↦ a)).IsCauchy := by
  rw [Sequence.IsCauchy.coe]
  intro ε hε
  refine ⟨0, ?_⟩
  intro j _ k _
  rw [Section_4_3.dist_eq]
  simpa using le_of_lt hε

public theorem Sequence.IsCauchy.neg (a:ℕ → ℚ) (ha: (Sequence.ofNatFun a).IsCauchy) :
    (Sequence.ofNatFun (-a)).IsCauchy := by
  have hmul := Sequence.IsCauchy.mul (Sequence.IsCauchy.const (-1)) ha
  have hfun : (fun _ ↦ (-1:ℚ)) * a = -a := by
    ext n
    simp [Pi.mul_apply, Pi.neg_apply]
  rwa [hfun] at hmul

/-- It may be possible to omit the {name (full := Sequence.IsCauchy)}`IsCauchy` hypothesis here. -/
public theorem Real.neg_LIM (a:ℕ → ℚ) (ha: (Sequence.ofNatFun a).IsCauchy) : -LIM a = LIM (-a) := by
  have hneg1 := Sequence.IsCauchy.const (-1)
  have hnegA := Sequence.IsCauchy.mul hneg1 ha
  have hfun : (fun _ ↦ (-1:ℚ)) * a = -a := by
    ext n
    simp [Pi.mul_apply, Pi.neg_apply]
  calc
    -LIM a = ((-1:ℚ):Real) * LIM a := rfl
    _ = LIM (fun _ ↦ (-1:ℚ)) * LIM a := by rw [ratCast_def]
    _ = LIM ((fun _ ↦ (-1:ℚ)) * a) := LIM_mul hneg1 ha
    _ = LIM (-a) := by rw [hfun]

public theorem Sequence.IsCauchy.sub {a b:ℕ → ℚ}
    (ha: (Sequence.ofNatFun a).IsCauchy) (hb: (Sequence.ofNatFun b).IsCauchy) :
    (Sequence.ofNatFun (a - b)).IsCauchy := by
  have hadd := Sequence.IsCauchy.add ha (Sequence.IsCauchy.neg b hb)
  have hfun : a + -b = a - b := by
    ext n
    ring
  rwa [hfun] at hadd

/-- {name}`LIM` distributes over subtraction -/
public theorem Real.LIM_sub {a b:ℕ → ℚ}
    (ha: (Sequence.ofNatFun a).IsCauchy) (hb: (Sequence.ofNatFun b).IsCauchy) :
    LIM a - LIM b = LIM (a - b) := by
  have hneg := Sequence.IsCauchy.neg b hb
  have hfun : a + -b = a - b := by
    ext n
    ring
  calc
    LIM a - LIM b = LIM a + -LIM b := sub_eq_add_neg _ _
    _ = LIM a + LIM (-b) := by rw [neg_LIM b hb]
    _ = LIM (a + -b) := LIM_add ha hneg
    _ = LIM (a - b) := by rw [hfun]

/-- {name (full := RatCast.ratCast)}`ratCast` distributes over subtraction -/
public theorem Real.ratCast_sub (a b:ℚ) : (a:Real) - (b:Real) = (a-b:ℚ) := by
  simp_rw [ratCast_def, LIM_sub (Sequence.IsCauchy.const a) (Sequence.IsCauchy.const b)]
  have hfun : (fun _ : ℕ ↦ a) - (fun _ : ℕ ↦ b) = (fun _ : ℕ ↦ a - b) := by
    ext n
    rfl
  rw [hfun]

/-- {name (full := RatCast.ratCast)}`ratCast` commutes with negation -/
public theorem Real.neg_ratCast (a:ℚ) : -(a:Real) = (-a:ℚ) := by
  have ha := Sequence.IsCauchy.const a
  simp_rw [ratCast_def, neg_LIM (fun _ ↦ a) ha]
  have hfun : -(fun _ : ℕ ↦ a) = (fun _ : ℕ ↦ -a) := by
    ext n
    rfl
  rw [hfun]

end Chapter5
