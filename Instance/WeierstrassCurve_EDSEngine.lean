-- Carved from Lemma/Definitions/Def_WeierstrassCurve_EDSEngine.lean: instance decls only.

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

@[expose] public section

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
