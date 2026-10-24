import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec19GradedQuotient
open DirectSum BigOperators


/--
[initialForm_nonZeroDivisor_intersection](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19GradedQuotient.lean)
-/
@[path]
lemma initialForm_nonZeroDivisor_intersection
  [CommRing A]
  {m : Ideal A}
  {a : A}
  {p : ℕ}
  {n : ℕ}
  {c : A}
-- given
  (hnd : InitialFormNonZeroDivisor m a p)
  (hn : p ≤ n)
  (hac : a * c ∈ m ^ n) :
-- imply
  c ∈ m ^ (n - p) := by
-- proof
  suffices h : ∀ j : ℕ, j ≤ n - p → c ∈ m ^ j from h (n - p) le_rfl
  intro j hj
  induction j with
  | zero => simp [Ideal.one_eq_top]
  | succ j ih =>
    have hj' : j ≤ n - p := Nat.le_of_succ_le hj
    have hcj := ih hj'
    have hjpn : j + p + 1 ≤ n := by omega
    have hacjp1 : a * c ∈ m ^ (j + p + 1) := Ideal.pow_le_pow_right hjpn hac
    exact hnd j c hcj hacjp1

/--
[lemma32_graded_quotient](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec19GradedQuotient.lean)
-/
@[path]
lemma lemma32_graded_quotient
  [CommRing A]
  {m : Ideal A}
  {a : A}
  {p : ℕ}
  {n : ℕ}
-- given
  (ha : a ∈ m ^ p)
  (hnd : InitialFormNonZeroDivisor m a p)
  (hn : p ≤ n) :
-- imply
  Ideal.span {a} ⊓ m ^ n = Ideal.span {a} * m ^ (n - p) := by
-- proof
  ext x
  simp only [Ideal.mem_inf, Ideal.mem_span_singleton]
  rw [Ideal.mem_span_singleton_mul]
  constructor
  ·
    rintro ⟨⟨c, rfl⟩, hx⟩
    exact ⟨c, initialForm_nonZeroDivisor_intersection m a p hnd n hn c hx, rfl⟩
  ·
    rintro ⟨c, hc, rfl⟩
    refine ⟨⟨c, rfl⟩, ?_⟩
    have hpow : m ^ p * m ^ (n - p) ≤ m ^ n := by
      rw [← pow_add]; exact le_of_eq (by congr 1; omega)
    exact hpow (Ideal.mul_mem_mul ha hc)


-- created on 2026-10-23
