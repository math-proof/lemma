import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.AffineCurve
open MvPolynomial Algebra
open scoped Cardinal


/--
[dim_affine_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineCurve.lean)
-/
@[path]
lemma dim_affine_space
  {k : Type}
  [Field k]
  {n : ℕ} :
-- imply
  Algebra.trdeg k (MvPolynomial (Fin n) k) = ↑n := by
-- proof
  simp [MvPolynomial.trdeg_of_isDomain]

/--
[quotient_eval_ker_isAlgebraic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AffineCurve.lean)
-/
@[path]
lemma quotient_eval_ker_isAlgebraic
  {k : Type}
  [Field k]
  {n : ℕ}
  {p : Fin n → k} :
-- imply
  Algebra.IsAlgebraic k (MvPolynomial (Fin n) k ⧸ RingHom.ker (MvPolynomial.eval p)) := by
-- proof
  constructor
  intro x
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective x
  rw [isAlgebraic_iff_isIntegral, ← hf]
  have : (Ideal.Quotient.mk (RingHom.ker (MvPolynomial.eval p))) f =
    algebraMap k _ (MvPolynomial.eval p f) := by
    show _ = (Ideal.Quotient.mk _) (MvPolynomial.C (MvPolynomial.eval p f))
    rw [Ideal.Quotient.eq]
    simp [RingHom.mem_ker, map_sub, MvPolynomial.eval_C]
  rwa [this]


-- created on 2026-10-23
