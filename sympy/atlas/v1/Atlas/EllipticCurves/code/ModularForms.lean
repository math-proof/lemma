/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/ModularForms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.EllipticCurves.code.FermatsLastTheorem
import Lemma.Complex.Atlas.v1.EllipticCurves.code.FermatsLastTheorem
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.ModularForms.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.Analytic.Order
import Mathlib.GroupTheory.Torsion
import Mathlib.LinearAlgebra.Dimension.Finrank

open scoped CongruenceSubgroup MatrixGroups ModularForm Topology Manifold

noncomputable section

section WeakModularForms

/-- A weak modular form of weight `k` for a subgroup `Γ ≤ GL(2, ℝ)`: a slash-invariant
function on the upper half plane that is holomorphic (`MDiff`), but without any
condition on growth at the cusps. -/
structure WeakModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) (k : ℤ) extends
    SlashInvariantForm Γ k where
  holo' : MDiff (⇑toSlashInvariantForm)

end WeakModularForms

section ModularForms

/-- Modular forms of weight `k` for the full modular group `SL(2, ℤ) = Γ(1)`. -/
abbrev ModularFormForSL2Z (k : ℤ) := ModularForm (Γ(1) : Subgroup SL(2, ℤ)) k

/-- Forgetful map: every modular form for `SL(2, ℤ)` is in particular a weak modular
form (we drop the boundedness-at-cusps condition). -/
def ModularFormForSL2Z.toWeakModularForm {k : ℤ} (f : ModularFormForSL2Z k) :
    WeakModularForm (Γ(1) : Subgroup SL(2, ℤ)) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'

end ModularForms

section CongruenceSubgroups

/-- Modular forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev ModularFormGamma0 (N : ℕ) (k : ℤ) :=
  ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

/-- Weak modular forms of weight `k` for `Γ₀(N)` (holomorphic and slash-invariant,
without cuspidal growth condition). -/
abbrev WeakModularFormGamma0 (N : ℕ) (k : ℤ) :=
  WeakModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

end CongruenceSubgroups

section CuspForms

/-- Cusp forms of weight `k` for the full modular group `SL(2, ℤ) = Γ(1)` (modular
forms vanishing at every cusp). -/
abbrev CuspFormForSL2Z (k : ℤ) := CuspForm (Γ(1) : Subgroup SL(2, ℤ)) k

/-- Cusp forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev CuspFormGamma0 (N : ℕ) (k : ℤ) :=
  CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

/-- A cusp form for `SL(2, ℤ)` is in particular a modular form (vanishing at cusps
implies boundedness at cusps). -/
def CuspFormForSL2Z.toModularFormForSL2Z {k : ℤ} (f : CuspFormForSL2Z k) :
    ModularFormForSL2Z k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'
  bdd_at_cusps' hc := ModularFormClass.bdd_at_cusps f hc

/-- A cusp form for `SL(2, ℤ)` is in particular a weak modular form (drop both the
boundedness and vanishing conditions at cusps). -/
def CuspFormForSL2Z.toWeakModularForm {k : ℤ} (f : CuspFormForSL2Z k) :
    WeakModularForm (Γ(1) : Subgroup SL(2, ℤ)) k where
  toSlashInvariantForm := f.toSlashInvariantForm
  holo' := f.holo'

end CuspForms

namespace FLT

/-- The Taylor–Wiles theorem: every semistable elliptic curve over `ℚ` is modular. -/
end FLT

namespace MinimalModel

/-- Predicate stating that an integral Weierstrass model `W` is a model for the
rational Weierstrass curve `E`, i.e. there is a `ℚ`-rational change of variables
taking `W` (viewed over `ℚ`) to `E`. -/
def IsModelFor (E : WeierstrassCurve.Affine ℚ) (W : WeierstrassCurve.Affine ℤ) : Prop :=
  ∃ C : WeierstrassCurve.VariableChange ℚ,
    C • (W.map (Int.castRingHom ℚ)) = E

/-- Structure encoding that `W` is a minimal integral model for `E`: it is a model
for `E` and its discriminant divides that of every other integral model of `E`. -/
structure IsMinimalModel (E : WeierstrassCurve.Affine ℚ)
    (W : WeierstrassCurve.Affine ℤ) : Prop where
  is_model_for : IsModelFor E W
  discriminant_dvd : ∀ W' : WeierstrassCurve.Affine ℤ, IsModelFor E W' → W.Δ ∣ W'.Δ

/-- The minimal discriminant of a rational Weierstrass curve: the discriminant of
its minimal integral model. -/
end MinimalModel

namespace EllipticCurveReduction

open MinimalModel

/-- The four possible reduction types of an elliptic curve at a prime:
good reduction, split multiplicative reduction, nonsplit multiplicative reduction,
or additive reduction. -/
inductive ReductionType where
  | good : ReductionType
  | splitMultiplicative : ReductionType
  | nonsplitMultiplicative : ReductionType
  | additive : ReductionType
  deriving DecidableEq, Repr

/-- The reduction type of an elliptic curve `E` over `ℚ` at the prime `p`, computed
from the reduction of its minimal model modulo `p`. -/
end EllipticCurveReduction

namespace EllipticCurve

open EllipticCurveReduction in
/-- An elliptic curve over `ℚ` is semistable if it has good or multiplicative
(but never additive) reduction at every prime. -/
end EllipticCurve

namespace EllipticCurveLFunction

open Complex Polynomial EllipticCurveReduction

/-- The trace of Frobenius of `E` at the prime `p`: at primes of good reduction
it equals `p + 1 − #E(𝔽_p)`, and at primes of bad reduction it takes the
conventional values `0` (additive), `1` (split multiplicative), or `−1`
(nonsplit multiplicative). -/
end EllipticCurveLFunction

namespace NewformQExpansion

open EllipticCurveLFunction EllipticCurveReduction

/-- An integral, normalized weight-2 newform: a level `N` together with integer
Fourier coefficients `a_n` with `a_0 = 0` and `a_1 = 1`. -/
structure IntegralWeight2Newform where
  level : ℕ+
  coeffs : ℕ → ℤ
  coeffs_zero : coeffs 0 = 0
  coeffs_one : coeffs 1 = 1

/-- The integer Fourier coefficients of the (conjectural) weight-2 newform
attached to the elliptic curve `E`. -/
end NewformQExpansion

namespace ModularEllipticCurve

open EllipticCurveLFunction EllipticCurveReduction NewformQExpansion

/-- An elliptic curve `E` over `ℚ` is modular if there exists an integral
weight-2 newform whose Fourier coefficients agree with the q-expansion
coefficients of `E`. -/
end ModularEllipticCurve

namespace ModularityTheorem

open EllipticCurveLFunction EllipticCurveReduction NewformQExpansion ModularEllipticCurve

/-- The L-function of a newform: the Dirichlet L-series with coefficients
`a_n ∈ ℂ`. -/
noncomputable def newformLFunction
    (f : IntegralWeight2Newform) (s : ℂ) : ℂ :=
  LSeries (fun n => (f.coeffs n : ℂ)) s

/-- An elliptic curve `E` has a modular L-function if its L-function equals
that of some newform whose level matches the conductor of `E`. -/
end ModularityTheorem

open ModularEllipticCurve in
/-- Global statement of the modularity theorem in the namespace's preferred form:
every elliptic curve over `ℚ` is modular. -/
namespace FaltingsTate

open EllipticCurveLFunction EllipticCurveReduction

/-- Predicate stating that `p` is a prime of good reduction for both `E₁` and
`E₂`. -/
end FaltingsTate

namespace IsogenyLFunction

open EllipticCurveLFunction EllipticCurveReduction

/-- Isogenous elliptic curves have the same trace of Frobenius at every prime. -/
end IsogenyLFunction

open EllipticCurveLFunction EllipticCurveReduction in
/-- Global re-statement: two elliptic curves over `ℚ` are isogenous iff they
have the same L-function. -/
namespace HeckeOperatorProperties

open Complex

/-- A complex lattice `Λ ⊂ ℂ`: a pair of complex periods `ω₁, ω₂` that are
ℝ-linearly independent. -/
@[ext]
structure ComplexLattice where
  ω₁ : ℂ
  ω₂ : ℂ
  indep : LinearIndependent ℝ ![ω₁, ω₂]

/-- The free abelian group on the set of complex lattices, viewed as the divisor
group of lattices. -/
abbrev DivL := FreeAbelianGroup ComplexLattice

/-- Coercion of a positive natural number `n` to a nonzero complex unit. -/
noncomputable def pnatToComplexUnits (n : ℕ+) : ℂˣ :=
  Units.mk0 (n : ℂ) (by exact_mod_cast n.ne_zero)

/-- The action of a nonzero complex scalar `l` on a complex lattice, scaling
both periods. -/
noncomputable def scaleLattice (l : ℂˣ) (L : ComplexLattice) : ComplexLattice where
  ω₁ := (l : ℂ) * L.ω₁
  ω₂ := (l : ℂ) * L.ω₂
  indep := by
    have hl : (l : ℂ) ≠ 0 := Units.ne_zero l
    let f : ℂ →ₗ[ℝ] ℂ := {
      toFun := fun x => (l : ℂ) * x
      map_add' := fun a b => by ring
      map_smul' := fun r x => Algebra.mul_smul_comm r (l : ℂ) x
    }
    have hf_ker : f.ker = ⊥ := by
      rw [LinearMap.ker_eq_bot']
      intro x hx
      simp only [f, LinearMap.coe_mk, AddHom.coe_mk] at hx
      exact (mul_eq_zero.mp hx).resolve_left hl
    have heq : ![(l : ℂ) * L.ω₁, (l : ℂ) * L.ω₂] = f ∘ ![L.ω₁, L.ω₂] := by
      ext i; fin_cases i <;> simp [f]
    rw [heq]
    exact L.indep.map' f hf_ker

/-- The Hecke operator `T_n` acting on the free abelian group of lattices: sends
each lattice to the formal sum of its index-`n` sublattices. -/
noncomputable def homothetyR (l : ℂˣ) : Module.End ℤ DivL :=
  (FreeAbelianGroup.map (scaleLattice l)).toIntLinearMap

/-- The absolute Galois group of `ℚ`, `Gal(ℚ̄/ℚ)`. -/
noncomputable def reductionModL (ℓ : ℕ) [Fact (Nat.Prime ℓ)] :
    GL (Fin 2) ℤ_[ℓ] →* GL (Fin 2) (ZMod ℓ) :=
  Matrix.GeneralLinearGroup.map PadicInt.toZMod

/-- The mod-`ℓ` Galois representation attached to `E`: the composition of the
`ℓ`-adic representation with reduction modulo `ℓ`. -/
end GaloisRepresentation

end

namespace NewformDefinition

open Complex Asymptotics Filter

/-- A formal Dirichlet series, wrapping a sequence of complex coefficients. -/
structure DirichletSeries where
  coeffs : ℕ → ℂ

/-- The value at `s` of a Dirichlet series, defined as the L-series of its
coefficient sequence. -/
noncomputable def DirichletSeries.eval (L : DirichletSeries) (s : ℂ) : ℂ :=
  LSeries L.coeffs s

/-- Summability of a Dirichlet series at `s`: the underlying L-series sum is
summable. -/
def DirichletSeries.summable (L : DirichletSeries) (s : ℂ) : Prop :=
  LSeriesSummable L.coeffs s

/-- The arithmetic rank of an elliptic curve over `ℚ`: the ℤ-rank of its
Mordell–Weil group modulo torsion. -/
noncomputable def arithmeticRank (E : WeierstrassCurve.Affine ℚ) [E.IsElliptic] : ℕ :=
  Module.finrank ℤ (E.Point ⧸ AddCommGroup.torsion E.Point)

/-- The arithmetic rank is realised by an additive isomorphism
`E(ℚ)/tors ≃ ℤ^{rank}`. -/
end WeakBSD

namespace HeckeAnalyticContinuation

open Complex

/-- Data for a cusp form: weight, level, and complex Fourier coefficients with
`a_0 = 0`. -/
structure CuspFormData where
  weight : ℕ
  level : ℕ+
  coeffs : ℕ → ℂ
  coeffs_zero : coeffs 0 = 0

/-- The L-function attached to a cusp form's coefficient data: the Dirichlet
L-series of its coefficients. -/
end HeckeAnalyticContinuation

namespace EulerProductNewform

open Complex HeckeAnalyticContinuation

/-- Data for a normalized newform: cusp-form data together with the
normalization `a_1 = 1`. -/
structure NewformData extends CuspFormData where
  coeffs_one : toCuspFormData.coeffs 1 = 1

/-- The principal Dirichlet character of conductor `N` at the prime `p`: equals
`0` if `p | N` and `1` otherwise. -/
noncomputable def principalDirichletChar (N : ℕ+) (p : ℕ) : ℂ :=
  if p ∣ (N : ℕ) then 0 else 1

/-- The local Euler factor of a newform at the prime `p`:
`(1 - a_p p^{-s} + χ(p) p^{k-1} p^{-2s})^{-1}`. -/
end EulerProductNewform

namespace ParityConjecture

open WeakBSD

/-- The root number `w(E) ∈ {±1}` of an elliptic curve over `ℚ`: the sign in
the functional equation of its L-function. -/
end ParityConjecture

namespace PeterssonInnerProduct

open Complex MeasureTheory
open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- Cusp forms of weight `k` for the congruence subgroup `Γ₀(N) ≤ SL(2, ℤ)`. -/
abbrev CuspFormGamma0 (N : ℕ) (k : ℤ) :=
  CuspForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k

/-- The Hecke operator `T_n` acting on weight-`k` modular forms for
`SL(2, ℤ)`. -/
end PeterssonInnerProduct

namespace SpectralTheorem

open LinearMap IsSymmetric Module.End

/-- The normalized (completed) L-function of an elliptic curve over `ℚ`:
`N^{s/2} (2π)^{-s} Γ(s) L(E, s)`. -/
noncomputable def cuspFormDataOfNewform (f : IntegralWeight2Newform) : CuspFormData where
  weight := 2
  level := f.level
  coeffs := fun n => (f.coeffs n : ℂ)
  coeffs_zero := by simp [f.coeffs_zero]

/-- The L-function of an elliptic curve over `ℚ` extends to an entire function on
`ℂ` agreeing with `L(E, s)` on the region of summability and satisfies the
functional equation `Λ(s) = w · Λ(2 - s)` with sign `w ∈ {±1}`. -/
end LFunctionAnalyticContinuation

namespace ModularForm

open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- Cusp forms of weight `k` for an arbitrary subgroup `Γ ≤ SL(2, ℤ)`. -/
abbrev CuspFormForSubgroup (Γ : Subgroup SL(2, ℤ)) (k : ℤ) :=
  CuspForm Γ k

end ModularForm

namespace HeckeEigenformBasis

open Complex
open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- The `n`-th q-expansion coefficient `a_n(f)` of a weight-`k` cusp form for
`SL(2, ℤ)`. -/
end HeckeEigenformBasis

namespace HeckeEigenvalueTheorem

open scoped CongruenceSubgroup MatrixGroups ModularForm
open Complex

/-- The `n`-th Fourier coefficient of a weight-`k` cusp form for `SL(2, ℤ)`. -/
end HeckeEigenvalueTheorem

namespace HeckeCoeffRelation

open scoped CongruenceSubgroup MatrixGroups ModularForm
open Complex HeckeEigenvalueTheorem PeterssonInnerProduct

/-- The Hecke operator at `n = 1` is the identity on cusp forms. -/
end HeckeCoeffRelation

namespace ModularFormDimension

open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- The number `ν₂(Γ)` of elliptic points of order `2` for `Γ ≤ SL(2, ℤ)`. -/
end ModularFormDimension

namespace HeckeNewformDecomposition

open Complex
open scoped CongruenceSubgroup MatrixGroups ModularForm

/-- The new subspace `S_k^{new}(Γ₀(N))` of cusp forms of weight `k` and level
`N`, complementary to the old subspace coming from divisors of `N`. -/
end HeckeNewformDecomposition
