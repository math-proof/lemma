/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/QuadraticForms/ThreeSquaresLegendreRecursion.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.NumberTheory.LegendreSymbol.Basic
import Def.NumberTheory.QuadraticForms.ThreeSquares
import Lemma.Nat.QuadraticForms.ThreeSquares
import Mathlib.Algebra.Quaternion
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.FieldTheory.Finite.Basic
import Abbrev.NumberTheory.QuadraticForms.ThreeSquaresLegendreRecursion


namespace MetaMathlibExt

def r3legQ {R : Type*} [Semiring R] (x : (R × R) × R) : R :=
  x.1.1 ^ 2 + x.1.2 ^ 2 + x.2 ^ 2

def r3legB {R : Type*} [Semiring R] (x y : (R × R) × R) : R :=
  x.1.1 * y.1.1 + x.1.2 * y.1.2 + x.2 * y.2

def r3legRed (p : ℕ) (x : r3legIntVec) : r3legModVec p :=
  (((x.1.1 : ZMod p), (x.1.2 : ZMod p)), (x.2 : ZMod p))

def r3legScale (c : ℤ) (x : r3legIntVec) : r3legIntVec :=
  ((c * x.1.1, c * x.1.2), c * x.2)

def r3legAdd {R : Type*} [Add R] (x y : (R × R) × R) : (R × R) × R :=
  ((x.1.1 + y.1.1, x.1.2 + y.1.2), x.2 + y.2)

def r3legSub {R : Type*} [Sub R] (x y : (R × R) × R) : (R × R) × R :=
  ((x.1.1 - y.1.1, x.1.2 - y.1.2), x.2 - y.2)

def r3legRep (n : ℕ) : Finset r3legIntVec :=
  ((((Finset.Icc (-(n : ℤ)) (n : ℤ)) ×ˢ (Finset.Icc (-(n : ℤ)) (n : ℤ))) ×ˢ
      (Finset.Icc (-(n : ℤ)) (n : ℤ))).filter
      (fun x => r3legQ x = (n : ℤ)))

def r3legPure (x : r3legIntVec) : Quaternion ℤ :=
  { re := 0, imI := x.1.1, imJ := x.1.2, imK := x.2 }

def r3legVec (q : Quaternion ℤ) : r3legIntVec :=
  ((q.imI, q.imJ), q.imK)

def r3legPhi (q : Quaternion ℤ) (x : r3legIntVec) : r3legIntVec :=
  r3legVec (q * r3legPure x * star q)

end MetaMathlibExt
