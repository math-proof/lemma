import Mathlib
import sympy.Basic
import Lemma.AlgebraicCurve.DivisorClassGroup


namespace Definitions
end Definitions
open Definitions
open AlgebraicCurve


/-- ported from external source -/
@[path]
private lemma main
  [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
  {x : F}
  {a : K}
-- given
  (hx : Transcendental K x) :
-- imply
  ∃ D : Divisor K F, ∀ v : Place K F, D v = max 0 (v.ord (x - algebraMap K F a)) := by
-- proof
  classical
    have hxa : x - algebraMap K F a ≠ 0 := by
      intro h
      apply hx
      rw [sub_eq_zero] at h
      rw [h]
      exact isAlgebraic_algebraMap a
    obtain ⟨P, hP, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (x - algebraMap K F a) hxa
    exact ⟨P.mapRange (fun n => max 0 n) (by simp), fun v => by rw [Finsupp.mapRange_apply, hP v]⟩


-- created on 2026-10-24
