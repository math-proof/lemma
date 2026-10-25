-- Carved from Lemma/Definitions/Def_WeierstrassCurve_EDSEngine.lean: instance decls only.
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


namespace WeierstrassCurve

instance instIsEllipticBaseChange {R : Type*} {A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] (W : WeierstrassCurve R) [W.IsElliptic] : (W.baseChange A).IsElliptic :=
  inferInstanceAs <| (W.map (algebraMap R A)).IsElliptic

end WeierstrassCurve


section PortEllSequenceUniversal

noncomputable section

open scoped Polynomial.Bivariate

namespace WeierstrassCurve


namespace Univ

open scoped Polynomial Polynomial.Bivariate
open Coeff

instance : CommRing Poly := Polynomial.commRing

instance : pointedCurve.IsElliptic where
  isUnit := isUnit_iff_ne_zero.mpr <| by

    simpa only [pointedCurve, baseChange, map_Δ, map_ne_zero_iff _ algebraMap_field_injective]
      using Δ_curve_ne_zero

open Polynomial (CC)

end Univ

open Univ
variable {R} [CommRing R] (W : WeierstrassCurve R)


end WeierstrassCurve

end

end PortEllSequenceUniversal


section PortEllSequenceZSMul

open scoped Polynomial.Bivariate

namespace WeierstrassCurve

open Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (f : R →+* S)

noncomputable section

variable {x y : R}

namespace Univ

variable {m n : ℤ}

open WeierstrassCurve (ψ φ ωe)

namespace Affine

variable (n)

variable {n}

open Affine.Point

open WeierstrassCurve.Affine in
instance : AddGroup (curve⟮Univ.Field⟯) := inferInstance

end Affine


end Univ

variable {W} (eqn : W.toAffine.Equation x y)

open Univ Jacobian

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

open Univ

end

end WeierstrassCurve

end PortEllSequenceZSMul

