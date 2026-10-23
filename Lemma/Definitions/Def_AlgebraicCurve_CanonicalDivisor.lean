import Mathlib
import Lemma.Definitions.Def_ModularCurve_CanonicalDivisor

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

class HasCanonicalDivisor : Prop where
  exists_divisor : ∀ ω : Ω[F⁄K], ω ≠ 0 → ∃ D : Divisor K F,
    ∀ v : Place K F, D v = v.ordDifferential ω

def canonicalDivisorOf [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : Divisor K F :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose

theorem canonicalDivisorOf_apply [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) :
    canonicalDivisorOf hω v = v.ordDifferential ω :=
  (HasCanonicalDivisor.exists_divisor ω hω).choose_spec v

def canonicalClass (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] : Pic K F :=
  letI := Classical.propDecidable
  if h : ∃ ω : Ω[F⁄K], ω ≠ 0 then QuotientAddGroup.mk (canonicalDivisorOf h.choose_spec)
  else 0

def genus (K F : Type*) [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)] : ℕ :=
  letI := Classical.propDecidable
  if h : ∃ ω : Ω[F⁄K], ω ≠ 0
  then (Divisor.degree (canonicalDivisorOf h.choose_spec) + 2).toNat / 2
  else 0

end AlgebraicCurve

end
