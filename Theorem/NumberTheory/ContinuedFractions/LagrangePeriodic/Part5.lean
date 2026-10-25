/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/ContinuedFractions/LagrangePeriodic.lean -/

/-
Author: Muse Spark 1.3
-/

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.ContinuedFractions.Computation.TerminatesIffRat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.FieldTheory.Minpoly.Basic
import Abbrev.Dynamics.EventuallyPeriodicSequence
import Lemma.Set.EventuallyPeriodicSequence
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Def.NumberTheory.ContinuedFractions.LagrangePeriodic.Part5
/-!
# Euler–Lagrange theorem on eventually periodic continued fractions

This file proves the Lagrange direction of the Euler–Lagrange characterization
of eventually periodic continued fractions: a real quadratic irrational has an
eventually periodic continued fraction
(`continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational`).

The canonical biconditional
(`continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational`) and the
Euler direction
(`isRealQuadraticIrrational_of_continuedFractionEventuallyPeriodic`) are proved
in `MathlibExt.NumberTheory.ContinuedFractions.EulerPeriodic`.

## Sources

* Amrik Singh Nimbran and Paul Levrie, "Patterns in Continued Fractions of
  Square Roots," Journal of Integer Sequences 26 (2023),
  <https://cs.uwaterloo.ca/journals/JIS/VOL26/Nimbran/nimbran14.tex>.
* The eventual-periodicity definition is lines 130–134; exact newline-terminated
  raw span SHA-256:
  `6d3b24948521d4d3fa03d6e17261c9442aa6cdf875126db573c9575a66623a7e`.
* The Euler–Lagrange statement is line 136; exact newline-terminated raw span
  SHA-256:
  `5be80578f3e620afa4d20050b29627a4c251e6ff852720806a9a42a0ff884b42`.
* Complete source file SHA-256:
  `08f38fd112c2dedb3802fe71799b670f6d2dbf5f49a89afdc0828156b8f56180`.
* Archive: `lagrange_periodic_cf_release_v2_D119163759`.
-/


namespace MetaMathlibExt

section

/-- The shift map sends each tail quotient to the next. -/
theorem xiShift_orbit (x : ℝ) (n : ℕ) :
    (⟨cfXi x (n + 1 + 1), n + 1, rfl⟩ : ↥(Set.range (fun n => cfXi x (n + 1))))
      = xiShift x ⟨cfXi x (n + 1), n, rfl⟩ := by
  apply Subtype.ext
  change cfXi x (n + 1 + 1) = 1 / (cfXi x (n + 1) - ⌊cfXi x (n + 1)⌋)
  have e : n + 1 + 1 = n + 2 := by omega
  rw [e]
  exact cfXi_step x n

/-- The tail complete quotients form an eventually periodic sequence. -/
theorem cfXi_eventually_periodic (x : ℝ) (hx : Irrational x) (a b c : ℤ)
    (hquad : (a : ℝ) * x ^ 2 + (b : ℝ) * x + (c : ℝ) = 0)
    (noroot : ∀ q : ℚ, (a : ℝ) * (((q : ℚ)) : ℝ) ^ 2 + (b : ℝ) * (((q : ℚ)) : ℝ)
      + (c : ℝ) ≠ 0)
    (M K : ℕ)
    (hA : ∀ n, (triA a b c x n).natAbs ≤ M)
    (hB : ∀ n, (triB a b c x n).natAbs ≤ K)
    (hC : ∀ n, (triC a b c x n).natAbs ≤ M) :
    IsEventuallyPeriodic (fun n => cfXi x (n + 1)) := by
  have hfin : (Set.range (fun n => cfXi x (n + 1))).Finite := by
    refine Set.Finite.subset (triU_finite M K) (fun y hy => ?_)
    obtain ⟨n, rfl⟩ := hy
    exact cfXi_mem_triU x hx a b c hquad noroot M K hA hB hC n
  have : Fintype ↥(Set.range (fun n => cfXi x (n + 1))) := hfin.fintype
  obtain ⟨p, n₀, hp, hper⟩ := IsEventuallyPeriodic.of_finite_orbit (xiShift x)
    (fun n : ℕ => ⟨cfXi x (n + 1), n, rfl⟩) (fun n => xiShift_orbit x n)
  refine IsEventuallyPeriodic.of_witness (n₀ := n₀) hp (fun n hn => ?_)
  exact congrArg Subtype.val (hper n hn)

/-- Lagrange direction of the Euler–Lagrange theorem: a real quadratic irrational
has an eventually periodic continued fraction. The canonical biconditional
(`continuedFractionEventuallyPeriodic_iff_isRealQuadraticIrrational`) and the
Euler direction are proved in
`MathlibExt.NumberTheory.ContinuedFractions.EulerPeriodic`.
-/
theorem continuedFractionEventuallyPeriodic_of_isRealQuadraticIrrational
    (x : ℝ) (h : IsRealQuadraticIrrational x) :
    ContinuedFractionEventuallyPeriodic x := by
  obtain ⟨hint, hdeg⟩ := h
  obtain ⟨a, b, c, ha, heq, hnoroot⟩ := quad_int_of_minpoly x hint hdeg
  have hirr : Irrational x := quad_irrational x hint hdeg
  have hnonterm : ¬ (GenContFract.of x).Terminates := by
    rw [GenContFract.terminates_iff_rat]
    intro hmem
    obtain ⟨q, hq⟩ := hmem
    apply hnoroot q
    rw [← hq]
    exact heq
  obtain ⟨M1, hM1⟩ := triA_bound x hirr a b c heq
  obtain ⟨K, hK⟩ := triB_bound x hirr a b c heq
  obtain ⟨M2, hM2⟩ := triC_bound x hirr a b c heq
  have hA : ∀ n, (triA a b c x n).natAbs ≤ max M1 M2 :=
    fun n => le_trans (hM1 n) (le_max_left _ _)
  have hC : ∀ n, (triC a b c x n).natAbs ≤ max M1 M2 :=
    fun n => le_trans (hM2 n) (le_max_right _ _)
  obtain ⟨p, n₀, hp, hper⟩ := cfXi_eventually_periodic x hirr a b c heq hnoroot
    (max M1 M2) K hA hK hC
  have hxi : ∀ n, n₀ ≤ n → cfXi x (n + p + 1) = cfXi x (n + 1) :=
    fun n hn => hper n hn
  refine ⟨hnonterm, IsEventuallyPeriodic.of_witness (n₀ := n₀ + 1) hp
    (fun m hm => ?_)⟩
  rw [partDens_eq_head x (m + p), partDens_eq_head x m]
  have hxi' : cfXi x (m + p) = cfXi x m := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    have e : n + 1 + p = n + p + 1 := by omega
    rw [e]
    exact hxi n (by omega)
  rw [hxi']

end
end MetaMathlibExt
