/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/DiscreteValuationRing/MaximalIdealPowQuotientTrace.lean -/

/-
Author: Muse Code
-/

import Mathlib.RingTheory.Trace.Quotient
import sympy.atlas.LinearAlgebra.Trace.InvariantSubmodule
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealGradedPieceMul
import sympy.atlas.RingTheory.DiscreteValuationRing.MaximalIdealPowFactor
/-!
# One-step trace recurrence for maximal-ideal-power quotients

Let `A` and `B` be commutative-domain discrete valuation rings with an
`A`-algebra structure on `B`. For each `n`, the canonical factor map from the
quotient by `map 𝔪A ⊔ 𝔪B ^ (n + 1)` to the quotient by `map 𝔪A ⊔ 𝔪B ^ n` is a
surjective `ResidueField A`-algebra hom. Under the containment hypothesis
`map 𝔪A ≤ 𝔪B ^ (n + 1)` and the residue-field linear-structure assumptions on
the graded piece (as in the main theorem below), its kernel is identified with
the `n`-th maximal-ideal graded piece of `B`. Left multiplication by a quotient
representative therefore has trace equal to the graded-piece trace plus the
trace on the target quotient.

This module is a prerequisite stage for the corrected ATLAS NumberTheoryI N261
upper different-exponent bound (Theorem 12.27), not the full N261 target. It
proves the one-step trace recurrence, the iterated quotient trace formula
by induction, the integral-trace residue bridge
`residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow`, and the
tame integral-trace surjectivity
`intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow`: under
`map 𝔪A = 𝔪B ^ e` and `IsUnit (e : B)`, the integral trace is surjective; the
different-ideal containment, either valuation bound, the tame-equality
characterization, and the wild mixed-characteristic fractional trace-dual
estimate remain deferred. The bridge controls the integral trace only modulo
`maximalIdeal A` and does not by itself prove the fractional-dual bound. The
surjectivity result is the tame input only: it is new supporting API, not an
ATLAS source theorem, and not a proof of the wild mixed-characteristic bound.

ATLAS source: [`v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean`, lines
1237--1324, at revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/DifferentDiscriminant.lean#L1237-L1324).
Those lines define the ramification/different valuations and state the target
bounds, but they do not state the trace recurrence proved here.

Source-to-API map: `trace_residueFieldMaximalIdealPowQuotient_succ`,
`trace_residueFieldMaximalIdealPowQuotient`,
`residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow`, and the
tame integral-trace surjectivity
`intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow` (under
`map 𝔪A = 𝔪B ^ e` and `IsUnit (e : B)`, the integral trace is surjective) are
new supporting API for the quotient-filtration route to the trace/different
estimate; the different containment, the valuation bounds, the tame-equality
characterization, and the fractional trace-dual estimate remain deferred. The
surjectivity result is the tame input only, not an ATLAS source theorem and not
a proof of the wild mixed-characteristic bound.

## Main results

* `trace_residueFieldMaximalIdealPowQuotient_succ`: the algebra trace of
  multiplication by a representative on quotient index `n + 1` equals the
  residue-field trace of the residue plus the algebra trace on quotient
  index `n`.
* `trace_residueFieldMaximalIdealPowQuotient`: the algebra trace of
  multiplication by a representative on quotient index `n` equals `n` times
  the residue-field trace of the residue.
* `residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow`:
  under `map 𝔪A = 𝔪B ^ e`, the residue of `Algebra.intTrace A B b` equals
  `e` times the residue-field trace of `residue B b`. This is a congruence
  modulo `maximalIdeal A` only; it does not prove the wild
  mixed-characteristic fractional-dual bound.
* `intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow`: under
  `map 𝔪A = 𝔪B ^ e` and `IsUnit (e : B)`, the integral trace is surjective.
  This is new supporting API for the tame input only; it is not an ATLAS
  source theorem and not a proof of the wild mixed-characteristic bound.
-/

open IsLocalRing

variable (A B : Type*) [CommRing A] [CommRing B] [IsDomain A] [IsDomain B]
  [IsDiscreteValuationRing A] [IsDiscreteValuationRing B] [Algebra A B]

/-- One-step trace recurrence across the maximal-ideal-power quotient tower:
the algebra trace of multiplication by the representative `b` on quotient
index `n + 1` splits as the residue-field trace of `residue B b` plus the
algebra trace of multiplication by the representative `b` on quotient index
`n`. The proof uses the factor map as the surjective intertwiner
(`map_mul` gives multiplication compatibility), identifies its kernel with
the graded piece, transports the kernel-restriction trace by conjugacy, and
applies the graded-piece trace theorem. This is new prerequisite
infrastructure for the corrected ATLAS N261 quotient-filtration route, not a
source theorem. -/
theorem trace_residueFieldMaximalIdealPowQuotient_succ
    (n : ℕ)
    (hSucc : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      maximalIdeal B ^ (n + 1))
    [IsLocalHom (algebraMap A B)]
    [Module (ResidueField A)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)]
    [IsScalarTower (ResidueField A) (ResidueField B)
      (IsDiscreteValuationRing.MaximalIdealGradedPiece B n)]
    [FiniteDimensional (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B (n + 1))]
    (b : B) :
    Algebra.trace (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
        (Ideal.Quotient.mk _ b) =
      Algebra.trace (ResidueField A) (ResidueField B)
        (IsLocalRing.residue B b) +
        Algebra.trace (ResidueField A)
          (ResidueFieldMaximalIdealPowQuotient A B n)
          (Ideal.Quotient.mk _ b) := by
  have hsurj : Function.Surjective
      (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap :=
    factorResidueFieldMaximalIdealPowQuotient_surjective A B n
  have hcomm :
      (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap.comp
        (Algebra.lmul (ResidueField A)
          (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
          (Ideal.Quotient.mk _ b)) =
      (Algebra.lmul (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B n)
        (Ideal.Quotient.mk _ b)).comp
        (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap := by
    apply LinearMap.ext
    intro x
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [LinearMap.comp_apply, Algebra.coe_lmul_eq_mul,
      LinearMap.mul_apply', AlgHom.toLinearMap_apply, ← map_mul,
      factorResidueFieldMaximalIdealPowQuotient_mk]
  have htrace :=
    LinearMap.trace_eq_trace_restrict_ker_add_of_surjective
      (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap
      (Algebra.lmul (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
        (Ideal.Quotient.mk _ b))
      (Algebra.lmul (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B n)
        (Ideal.Quotient.mk _ b))
      hsurj hcomm
  have hker : ∀ hi : LinearMap.ker
        (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap ≤
        (LinearMap.ker
          (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap).comap
          (Algebra.lmul (ResidueField A)
            (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
            (Ideal.Quotient.mk _ b)),
      LinearMap.trace (ResidueField A)
          (LinearMap.ker
            (factorResidueFieldMaximalIdealPowQuotient A B n).toLinearMap)
          ((Algebra.lmul (ResidueField A)
            (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
            (Ideal.Quotient.mk _ b)).restrict hi) =
        Algebra.trace (ResidueField A) (ResidueField B)
          (IsLocalRing.residue B b) := by
    intro hi
    have hbridge :
        (residueFieldLinearEquivMaximalIdealGradedPieceKerFactor A B n
          hSucc).conj
          ((IsDiscreteValuationRing.residueFieldMulMaximalIdealGradedPiece B
              (IsLocalRing.residue B b) n).restrictScalars
            (ResidueField A)) =
        (Algebra.lmul (ResidueField A)
          (ResidueFieldMaximalIdealPowQuotient A B (n + 1))
          (Ideal.Quotient.mk _ b)).restrict hi := by
      apply LinearMap.ext
      intro x
      obtain ⟨y, rfl⟩ :=
        (residueFieldLinearEquivMaximalIdealGradedPieceKerFactor A B n
          hSucc).surjective x
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      apply Subtype.ext
      simp only [LinearEquiv.conj_apply_apply,
        LinearEquiv.symm_apply_apply, LinearMap.restrictScalars_apply,
        IsDiscreteValuationRing.residueFieldMulMaximalIdealGradedPiece_residue_mk,
        residueFieldLinearEquivMaximalIdealGradedPieceKerFactor_mk,
        LinearMap.restrict_apply, Algebra.coe_lmul_eq_mul,
        LinearMap.mul_apply', Submodule.coe_smul, smul_eq_mul, ← map_mul]
    rw [← hbridge, LinearMap.trace_conj',
      IsDiscreteValuationRing.trace_residueFieldMulMaximalIdealGradedPiece]
  simp only [Algebra.trace_apply] at htrace hker ⊢
  rw [htrace, hker]

/-- Iterated quotient trace formula: the algebra trace of multiplication by
the representative `b` on quotient index `n` equals `n` times the
residue-field trace of `residue B b`. The proof is by induction on `n`: at
index zero the defining ideal is the whole ring so the representative is
zero, and the successor case combines the one-step recurrence
`trace_residueFieldMaximalIdealPowQuotient_succ` with the induction
hypothesis. The graded-piece module/tower hypotheses of the one-step
recurrence are installed locally from the canonical restriction of scalars
along `algebraMap (ResidueField A) (ResidueField B)`, so they do not appear
in the public signature. This is new prerequisite infrastructure for the
corrected ATLAS N261 quotient-filtration route, not a source theorem. -/
theorem trace_residueFieldMaximalIdealPowQuotient
    (n : ℕ)
    (h : Ideal.map (algebraMap A B) (maximalIdeal A) ≤ maximalIdeal B ^ n)
    [IsLocalHom (algebraMap A B)]
    [FiniteDimensional (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B n)]
    (b : B) :
    Algebra.trace (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B n)
        (Ideal.Quotient.mk _ b) =
      n • Algebra.trace (ResidueField A) (ResidueField B)
        (IsLocalRing.residue B b) := by
  have key : ∀ (m : ℕ) (_ : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      maximalIdeal B ^ m)
      [FiniteDimensional (ResidueField A)
        (ResidueFieldMaximalIdealPowQuotient A B m)] (c : B),
      Algebra.trace (ResidueField A)
          (ResidueFieldMaximalIdealPowQuotient A B m)
          (Ideal.Quotient.mk _ c) =
        m • Algebra.trace (ResidueField A) (ResidueField B)
          (IsLocalRing.residue B c) := by
    intro m
    induction m with
    | zero =>
      intro _ _ c
      have htop : (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔
          maximalIdeal B ^ 0 : Ideal B) = ⊤ := by simp
      have hmk : (Ideal.Quotient.mk _ c :
          ResidueFieldMaximalIdealPowQuotient A B 0) = 0 := by
        rw [Ideal.Quotient.eq_zero_iff_mem, htop]
        exact Submodule.mem_top
      simp [hmk]
    | succ m ih =>
      intro hm hfd c
      have hLow : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
          maximalIdeal B ^ m :=
        le_trans hm (Ideal.pow_le_pow_right m.le_succ)
      have hfdL : FiniteDimensional (ResidueField A)
          (ResidueFieldMaximalIdealPowQuotient A B m) :=
        FiniteDimensional.of_surjective
          (factorResidueFieldMaximalIdealPowQuotient A B m).toLinearMap
          (factorResidueFieldMaximalIdealPowQuotient_surjective A B m)
      let hmod : Module (ResidueField A)
          (IsDiscreteValuationRing.MaximalIdealGradedPiece B m) :=
        Module.compHom _ (algebraMap (ResidueField A) (ResidueField B))
      have htower : IsScalarTower (ResidueField A) (ResidueField B)
          (IsDiscreteValuationRing.MaximalIdealGradedPiece B m) :=
        IsScalarTower.of_compHom (ResidueField A) (ResidueField B)
          (IsDiscreteValuationRing.MaximalIdealGradedPiece B m)
      rw [trace_residueFieldMaximalIdealPowQuotient_succ A B m hm c, ih hLow c,
        add_smul, one_smul, add_comm _ _]
  exact key n h b

/-- Integral-trace residue bridge: under `map 𝔪A = 𝔪B ^ e`, the residue of
`Algebra.intTrace A B b` equals `e` times the residue-field trace of
`residue B b`. The proof combines Mathlib's quotient-trace identity
`Algebra.trace_quotient_eq_of_isDedekindDomain` (at `p := maximalIdeal A`,
whose quotient is `ResidueField A`) with the iterated quotient trace formula
`trace_residueFieldMaximalIdealPowQuotient`: since `he` collapses the defining
ideal `map 𝔪A ⊔ 𝔪B ^ e` to `map 𝔪A`, the custom quotient is
`ResidueField A`-algebra equivalent to `B ⧸ map 𝔪A` via
`Ideal.quotEquivOfEq` (fixing representatives, with scalar compatibility
checked on representatives as in
`factorResidueFieldMaximalIdealPowQuotient`), and trace conjugacy
(`Algebra.trace_eq_of_algEquiv`) transports the Mathlib identity to the
custom quotient. The DVR hypotheses supply the Dedekind and integrally-closed
instances. This is new bridge infrastructure for the corrected ATLAS N261
quotient-filtration route, not a source theorem: it controls the integral
trace only modulo `maximalIdeal A` and does not prove the wild
mixed-characteristic fractional-dual bound. -/
theorem residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow
    (e : ℕ)
    [Module.IsTorsionFree A B] [Module.Finite A B]
    (he : Ideal.map (algebraMap A B) (maximalIdeal A) =
      maximalIdeal B ^ e)
    (b : B) :
    residue A (Algebra.intTrace A B b) =
      e • Algebra.trace (ResidueField A)
        (ResidueField B) (residue B b) := by
  have hle : Ideal.map (algebraMap A B) (maximalIdeal A) ≤
      maximalIdeal B ^ e := he ▸ le_rfl
  have hI : (Ideal.map (algebraMap A B) (maximalIdeal A) ⊔ maximalIdeal B ^ e :
      Ideal B) = Ideal.map (algebraMap A B) (maximalIdeal A) := by
    rw [he, sup_idem]
  have hMathlib := Algebra.trace_quotient_eq_of_isDedekindDomain (R := A) (S := B)
    (p := maximalIdeal A) (x := b)
  let : IsScalarTower A (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B e) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Module.Finite (ResidueField A)
      (ResidueFieldMaximalIdealPowQuotient A B e) :=
    Module.Finite.of_restrictScalars_finite A _ _
  have hIter := trace_residueFieldMaximalIdealPowQuotient A B e hle b
  let : Algebra (ResidueField A)
      (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
    inferInstanceAs (Algebra (A ⧸ maximalIdeal A) _)
  let e₂ : ResidueFieldMaximalIdealPowQuotient A B e ≃ₐ[ResidueField A]
      (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A)) :=
    { Ideal.quotEquivOfEq hI with
      commutes' := fun r => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        rfl }
  have hmk : e₂ (Ideal.Quotient.mk _ b) = Ideal.Quotient.mk _ b := rfl
  have hconj := Algebra.trace_eq_of_algEquiv e₂ (Ideal.Quotient.mk _ b)
  rw [hmk] at hconj
  have hres : residue A (Algebra.intTrace A B b) =
      Algebra.trace (ResidueField A)
        (B ⧸ Ideal.map (algebraMap A B) (maximalIdeal A))
        (Ideal.Quotient.mk _ b) := hMathlib.symm
  rw [hres, hconj]
  exact hIter

/-- Tame integral-trace surjectivity: under `map 𝔪A = 𝔪B ^ e` with
`IsUnit (e : B)`, the integral trace `Algebra.intTrace A B` is surjective.
Separability supplies a residue element of trace one, lifted to `b : B`;
since `e` is a unit, the bridge identity
`residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow` makes
`Algebra.intTrace A B b` a unit, and scaling `b` by an arbitrary `a` against
that unit hits every target. The `IsUnit (e : B)` form is ergonomic for the
eventual tame ramification criterion; localness makes it equivalent to
unitness in `A`. This proves the tame trace-surjectivity input only: it does
not prove the mixed-characteristic wild bound, nor ATLAS's false exact wild
equality. -/
theorem intTrace_surjective_of_isUnit_natCast_of_map_maximalIdeal_eq_pow
    (e : ℕ)
    [Module.IsTorsionFree A B] [Module.Finite A B]
    [Algebra.IsSeparable (ResidueField A) (ResidueField B)]
    (heUnit : IsUnit (e : B))
    (he : Ideal.map (algebraMap A B) (maximalIdeal A) =
      maximalIdeal B ^ e) :
    Function.Surjective (Algebra.intTrace A B) := by
  obtain ⟨r, hr⟩ := Algebra.trace_surjective
    (ResidueField A) (ResidueField B) (1 : ResidueField A)
  obtain ⟨b, hb⟩ := residue_surjective r
  have heUnitA : IsUnit (e : A) := by
    rw [← isUnit_map_iff (algebraMap A B) (e : A)]
    simpa only [map_natCast] using heUnit
  have hbTrace : IsUnit (Algebra.intTrace A B b) := by
    rw [← residue_ne_zero_iff_isUnit]
    rw [residue_intTrace_eq_nsmul_trace_residue_of_map_maximalIdeal_eq_pow
      A B e he b, hb, hr]
    simpa only [nsmul_eq_mul, mul_one, map_natCast] using
      (heUnitA.map (residue A)).ne_zero
  intro a
  obtain ⟨u, hu⟩ := hbTrace
  refine ⟨(a * ↑u⁻¹) • b, ?_⟩
  rw [map_smul, ← hu, smul_eq_mul, mul_assoc, Units.inv_mul, mul_one]
