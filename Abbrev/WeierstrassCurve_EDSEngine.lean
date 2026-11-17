module

public import Mathlib.NumberTheory.EllipticDivisibilitySequence
public import Instance.Compat_Mathlib430
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.FieldSimp
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.Data.Nat.Factorization.Induction
public import Mathlib.Logic.Embedding.Set
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Module.Torsion.Basic
public import Inductive.WeierstrassCurve_EDSEngine_Param
public import Inductive.WeierstrassCurve_Coeff
public import Macro.WeierstrassCurve_EDSEngine
public import Instance.WeierstrassCurve_EDSEngine

namespace WeierstrassCurve.Affine

scoped notation3:max W' "⟮" S "⟯" =>
  WeierstrassCurve.Affine.Point (WeierstrassCurve.Affine.baseChange W' S)

end WeierstrassCurve.Affine

namespace WeierstrassCurve

end WeierstrassCurve


section PortEllSequenceCore

universe u v w

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : ℤ → R)
variable {F} [FunLike F R S] [RingHomClass F R S] (f : F)

open scoped nonZeroDivisors

namespace EllSequence

section transf

variable (a b c d : ℤ)


end transf

section Rel₄OfValid
end Rel₄OfValid

section Perm

end Perm

end EllSequence

open EllSequence

variable {W}

namespace IsEllSequence'

open EllSequence

variable (ell : IsEllSequence' W)
end IsEllSequence'

variable (b c d : R)

section Complement

variable (b c d : R) (m : ℤ)

namespace EllSequence


end EllSequence

end Complement

section Map

variable {b c d}

end Map

section

variable {b c d} {U : ℤ → R} (ellW : IsEllSequence' W) (ellU : IsEllSequence' U)
open MvPolynomial

section Divisibility

variable (one : W 1 ∈ R⁰) (two : W 2 ∈ R⁰)
  (dvd₁₂ : W 1 ∣ W 2) (dvd₁₃ : W 1 ∣ W 3) (dvd₂₄ : W 2 ∣ W 4)

section Complement


namespace EllSequence

variable (b c d)

end EllSequence

end Complement

end Divisibility

section
end

end

end PortEllSequenceCore

section PortEllSequenceUniversal

@[expose] public noncomputable section

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

namespace Affine.CoordinateRing

end Affine.CoordinateRing

namespace Univ

open scoped Polynomial Polynomial.Bivariate
open Coeff

abbrev Poly : Type := (MvPolynomial Coeff ℤ)[X][Y]

end Univ

namespace Univ

variable (x y : R)

end Univ

end WeierstrassCurve

end

end PortEllSequenceUniversal

section PortEllSequenceDivisionPolys

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

noncomputable section

end

section Map

variable (f : R →+* S)

end Map

end WeierstrassCurve

end PortEllSequenceDivisionPolys

section PortEllSequenceZSMul

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

noncomputable section

variable {x y : R}

namespace Univ

namespace Affine

variable (n)

end Affine

namespace Jacobian

open WeierstrassCurve.Jacobian

end Jacobian

end Univ

end

end WeierstrassCurve

end PortEllSequenceZSMul

section PortEllSequenceAffineBridge

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve


end WeierstrassCurve

end PortEllSequenceAffineBridge
