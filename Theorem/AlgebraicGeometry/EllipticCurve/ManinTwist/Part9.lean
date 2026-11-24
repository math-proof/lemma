module
public import Def.AlgebraicGeometry.EllipticCurve.ManinSequence
public import Theorem.Int.EllipticCurve.ManinSequence
public import Theorem.Polynomial.PrimitiveTripleManinProjectiveDegreeEllipticCurve.of.All_False.Ne_0
public import Theorem.Scheme.EllipticCurve.VariableChangePoint
public import Theorem.Nat.FrobeniusTrace.eq.SubAddCardF1CardPoint.of.AffineF
public import Def.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree
public import Def.AlgebraicGeometry.EllipticCurve.VariableChangePoint.Part3
public import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Def.AlgebraicGeometry.EllipticCurve.PointCount
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.AddSubMap
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.Tactic.ComputeDegree
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Def.AlgebraicGeometry.EllipticCurve.ManinTwist.Part9
open Polynomial
open MathlibExt.AlgebraicGeometry.EllipticCurve.ManinProjectiveDegree


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/AlgebraicGeometry/EllipticCurve/ManinTwist.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/
/-!
# Manin's elementary proof in odd characteristic

This file develops Manin's quadratic-twist proof of the Hasse bound over finite fields of odd
characteristic.
-/
namespace MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist

noncomputable section

universe u

variable {F : Type u} [Field F]

lemma num_natDegree_gt_denom_natDegree [Finite F]
    (hchar : ringChar F ≠ 2) (W : WeierstrassCurve F)
    [W.IsCharNeTwoNF] [W.IsElliptic]
    {n : ℤ} {x y : RatFunc F}
    {hxy : (twist W).toAffine.Nonsingular x y}
    (hn : point hchar W n = .some x y hxy) :
    (RatFunc.denom (x / cubicRat W)).natDegree <
      (RatFunc.num (x / cubicRat W)).natDegree := by
  have hnotBad := point_not_badAtInfinity hchar W n
  have hnotLe : ¬(paperX W x).intDegree ≤ 0 := by
    intro hdegree
    apply hnotBad
    rw [hn]
    exact hdegree
  have hpos : 0 < (paperX W x).intDegree := lt_of_not_ge hnotLe
  unfold paperX RatFunc.intDegree at hpos
  omega

lemma d_zero [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    d hchar W 0 = Nat.card F := by
  rw [d, point]
  simp only [zero_zsmul, add_zero, P₀, WeierstrassCurve.Affine.Point.mk]
  have hx : pZeroX W / cubicRat W = RatFunc.X ^ Nat.card F := by
    rw [div_eq_iff (cubicRat_ne_zero W)]
    simp only [pZeroX]
    ring
  rw [hx]
  change
    (RatFunc.num ((algebraMap F[X] (RatFunc F) X) ^ Nat.card F)).natDegree =
      Nat.card F
  rw [← map_pow, RatFunc.num_algebraMap, Polynomial.natDegree_X_pow]

lemma d_eq_zero_iff_point_eq_zero [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic]
    (n : ℤ) :
    d hchar W n = 0 ↔ point hchar W n = 0 := by
  cases hp : point hchar W n with
  | zero =>
      constructor
      · exact fun _ ↦ WeierstrassCurve.Affine.Point.zero_def.symm
      · intro _
        simp [d, hp]
  | some x y hxy =>
      have hdeg := num_natDegree_gt_denom_natDegree hchar W hp
      constructor
      · intro hd
        simp only [d, hp] at hd
        omega
      · exact fun hpzero ↦ (WeierstrassCurve.Affine.Point.some_ne_zero hxy hpzero).elim

lemma noAdjacentZeros [Finite F] (hchar : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsCharNeTwoNF] [W.IsElliptic] :
    ∀ n, d hchar W n = 0 → d hchar W (n + 1) = 0 → False := by
  intro n hn hn1
  have hp := (d_eq_zero_iff_point_eq_zero hchar W n).mp hn
  have hp1 := (d_eq_zero_iff_point_eq_zero hchar W (n + 1)).mp hn1
  apply Q_ne_zero W
  have hs := point_add_one hchar W n
  rw [hp, hp1] at hs
  simpa using hs.symm

end
end MathlibExt.AlgebraicGeometry.EllipticCurve.ManinTwist
