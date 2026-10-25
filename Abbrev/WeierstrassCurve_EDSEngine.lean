import Mathlib.NumberTheory.EllipticDivisibilitySequence
import Instance.Compat_Mathlib430
import Mathlib.Algebra.Ring.NegOnePow
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.FieldSimp
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.Jacobian.Point
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Logic.Embedding.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.Card
import Mathlib.Algebra.Module.Torsion.Basic
import Inductive.WeierstrassCurve_EDSEngine_Param
import Inductive.WeierstrassCurve_Coeff
import Macro.WeierstrassCurve_EDSEngine
import Instance.WeierstrassCurve_EDSEngine

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

noncomputable section

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
