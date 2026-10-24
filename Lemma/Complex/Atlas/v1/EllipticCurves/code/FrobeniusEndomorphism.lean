import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.FrobeniusEndomorphism
open Polynomial FrobeniusEndomorphism


namespace FrobeniusEndomorphism

/--
[pointMap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
lemma pointMap_zero
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  [DecidableEq F]
-- given
  (hφ : FixesCoeffs W φ)
  (hφ_inj : Function.Injective φ) :
-- imply
  pointMap hφ hφ_inj .zero = .zero :=
-- proof
  rfl

end FrobeniusEndomorphism

namespace FrobeniusEndomorphism

/--
[pointMap_some](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
lemma pointMap_some
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  [DecidableEq F]
  {x y : F}
-- given
  (hφ : FixesCoeffs W φ)
  (hφ_inj : Function.Injective φ)
  (h : W.Nonsingular x y) :
-- imply
  pointMap hφ hφ_inj (.some x y h) = .some (φ x) (φ y) (nonsingular_preserved hφ hφ_inj h) :=
-- proof
  rfl

end FrobeniusEndomorphism

namespace FrobeniusEndomorphism

/--
[frobeniusPointMap_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
lemma frobeniusPointMap_zero
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  [DecidableEq F]
  {p n : ℕ}
  [Fintype F]
  [Fact (Nat.Prime p)]
  [CharP F p]
  {L : Type u}
  [Field L]
  [DecidableEq L]
  [Algebra F L]
  [CharP L p]
  {W : WeierstrassCurve.Affine F}
-- given
  (hcard : Fintype.card F = p ^ n) :
-- imply
  frobeniusPointMap (L := L) hcard W .zero = .zero :=
-- proof
  rfl

end FrobeniusEndomorphism

namespace FrobeniusEndomorphism

/--
[frobeniusPointMap_some](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
lemma frobeniusPointMap_some
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  [DecidableEq F]
  {p n : ℕ}
  [Fintype F]
  [Fact (Nat.Prime p)]
  [CharP F p]
  {L : Type u}
  [Field L]
  [DecidableEq L]
  [Algebra F L]
  [CharP L p]
  {W : WeierstrassCurve.Affine F}
  {x y : L}
-- given
  (hcard : Fintype.card F = p ^ n)
  (h : (baseChange W (L := L)).Nonsingular x y) :
-- imply
  frobeniusPointMap hcard W (.some x y h) = .some (x ^ (p ^ n)) (y ^ (p ^ n)) (nonsingular_preserved (fixesCoeffs_iterateFrobenius hcard W) (iterateFrobenius L p n).injective h) := by
-- proof
  simp [frobeniusPointMap, pointMap, iterateFrobenius]

end FrobeniusEndomorphism

/--
[evalEval_polynomial_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
private lemma evalEval_polynomial_map_eq
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  {x y : F}
-- given
  (hφ : FixesCoeffs W φ) :
-- imply
  Polynomial.evalEval (φ x) (φ y) W.polynomial = φ (Polynomial.evalEval x y W.polynomial) := by
-- proof
  apply FrobeniusEndomorphism.evalEval_polynomial_map hφ x y

/--
[equation_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
private lemma equation_preserved_eq
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  {x y : F}
-- given
  (hφ : FixesCoeffs W φ)
  (h : W.Equation x y) :
-- imply
  W.Equation (φ x) (φ y) := by
-- proof
  apply FrobeniusEndomorphism.equation_preserved hφ h

/--
[evalEval_polynomialX_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
private lemma evalEval_polynomialX_map_eq
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  {x y : F}
-- given
  (hφ : FixesCoeffs W φ) :
-- imply
  Polynomial.evalEval (φ x) (φ y) W.polynomialX = φ (Polynomial.evalEval x y W.polynomialX) := by
-- proof
  apply FrobeniusEndomorphism.evalEval_polynomialX_map hφ x y

/--
[evalEval_polynomialY_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
private lemma evalEval_polynomialY_map_eq
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  {x y : F}
-- given
  (hφ : FixesCoeffs W φ) :
-- imply
  Polynomial.evalEval (φ x) (φ y) W.polynomialY = φ (Polynomial.evalEval x y W.polynomialY) := by
-- proof
  apply FrobeniusEndomorphism.evalEval_polynomialY_map hφ x y

/--
[nonsingular_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
private lemma nonsingular_preserved_eq
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  {x y : F}
-- given
  (hφ : FixesCoeffs W φ)
  (hφ_inj : Function.Injective φ)
  (h : W.Nonsingular x y) :
-- imply
  W.Nonsingular (φ x) (φ y) := by
-- proof
  apply FrobeniusEndomorphism.nonsingular_preserved hφ hφ_inj h

/--
[iterateFrobenius_algebraMap](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
private lemma iterateFrobenius_algebraMap_eq
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  [DecidableEq F]
  {p n : ℕ}
  [Fintype F]
  [Fact (Nat.Prime p)]
  [CharP F p]
  {L : Type u}
  [Field L]
  [DecidableEq L]
  [Algebra F L]
  [CharP L p]
  {a : F}
-- given
  (hcard : Fintype.card F = p ^ n) :
-- imply
  iterateFrobenius L p n (algebraMap F L a) = algebraMap F L a := by
-- proof
  apply FrobeniusEndomorphism.iterateFrobenius_algebraMap hcard a

/--
[fixesCoeffs_iterateFrobenius](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FrobeniusEndomorphism.lean)
-/
@[path]
private lemma fixesCoeffs_iterateFrobenius_eq
  {F : Type u}
  [Field F]
  {W : WeierstrassCurve.Affine F}
  {φ : F →+* F}
  [DecidableEq F]
  {p n : ℕ}
  [Fintype F]
  [Fact (Nat.Prime p)]
  [CharP F p]
  {L : Type u}
  [Field L]
  [DecidableEq L]
  [Algebra F L]
  [CharP L p]
  {W : WeierstrassCurve.Affine F}
-- given
  (hcard : Fintype.card F = p ^ n) :
-- imply
  FixesCoeffs (baseChange W (L := L)) (iterateFrobenius L p n) where fix_a₁ := by
-- proof
  apply FrobeniusEndomorphism.fixesCoeffs_iterateFrobenius hcard W


-- created on 2026-10-23
