import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.ArithmeticGeometry.code.BoundedHeightFinite
open TateTheorem CanonicalHeight Filter


/--
[bounded_canonical_height_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/BoundedHeightFinite.lean)
-/
@[path]
lemma bounded_canonical_height_finite
  [Field K]
  [NumberField K]
  {W : WeierstrassCurve K}
  [W.IsElliptic]
  {B : ℝ}
-- given
  (h : W.toAffine.Point → ℝ)
  (hWeil : IsWeilHeightOnCurve W h) :
-- imply
  {P : W.toAffine.Point | EllipticCurve.NeronTateHeight W h hWeil P ≤ B}.Finite := by
-- proof
  obtain ⟨C, hC⟩ := hWeil.doubling_bound
  let φ : W.toAffine.Point → W.toAffine.Point := fun P => (2 : ℤ) • P
  have hbound : ∀ P, |h (φ P) - 4 * h P| ≤ C := hC
  have htate := tate_theorem φ h 4 (by norm_num : (1 : ℝ) < 4) C hbound
  have hcompare := htate.2.1
  have key : ∀ Q : W.toAffine.Point,
    atTop.limUnder (tateSeq φ h 4 Q) =
    EllipticCurve.NeronTateHeight W h hWeil Q := by
    intro Q
    unfold EllipticCurve.NeronTateHeight canonicalHeight
    congr 1
    funext n
    unfold tateSeq canonicalHeightSeq
    congr 1
    congr 1
    induction n with
    | zero => simp [Function.iterate_zero]
    | succ n ih =>
      rw [Function.iterate_succ', Function.comp_apply, ih]
      show (2 : ℤ) • ((2 : ℤ) ^ n • Q) = (2 : ℤ) ^ (n + 1) • Q
      rw [← mul_smul, pow_succ']
  apply Set.Finite.subset (hWeil.northcott (B + C / (4 - 1)))
  intro P hP
  simp only [Set.mem_setOf_eq] at hP ⊢
  rw [← key P] at hP
  have hab := hcompare P
  rw [abs_le] at hab
  linarith [hab.2]


-- created on 2026-10-23
