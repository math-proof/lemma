-- Carved from Lemma/Definitions/Def_EllipticCurve_FunctionFieldPullback.lean: instance decls only.
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Tactic.FieldSimp

open Polynomial
open scoped Polynomial.Bivariate

namespace WeierstrassCurve.Affine.CoordinateRing

variable {K : Type*} [Field K] {W : Affine K}

instance moduleFinite : Module.Finite K[X] W.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W)

instance isIntegral : Algebra.IsIntegral K[X] W.CoordinateRing :=
  Algebra.IsIntegral.of_finite K[X] W.CoordinateRing

end WeierstrassCurve.Affine.CoordinateRing

namespace WeierstrassCurve.Affine


section Generic

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]

noncomputable instance instDecidableEqFunctionField : DecidableEq (W⁄K).FunctionField :=
  Classical.decEq _

end Generic


end WeierstrassCurve.Affine

open Polynomial


open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero


