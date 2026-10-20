/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean -/

import Mathlib.NumberTheory.Ostrowski
import Mathlib.NumberTheory.Padics.PadicNumbers

/-!
# Rational places and completed fields

Source: arXiv:2607.14033, `pq-work-rank0-sha1.tex`, lines 237--240:

> Let M_Q be the set of all inequivalent normalised absolute values on Q.
> It consists of the ordinary absolute value, along with one non-archimedean
> absolute value for each prime number l.

`M_ℚ` is formalised as `Rat.Place` and `ℚ_v` as `CompletedField v`
(`ℝ` at infinity, `ℚ_[p]` at a prime), reusing
`Rat.AbsoluteValue.real` and `Rat.AbsoluteValue.padic`.
-/

namespace Rat

/-- Index for `M_ℚ`: inequivalent normalised absolute values on `ℚ`.

* `infinite` is the ordinary archimedean absolute value.
* `finite prime` is the `p`-adic absolute value for `prime = ⟨p, hp⟩`.
-/
inductive Place : Type where
  | infinite : Place
  | finite : (prime : Nat.Primes) → Place
  deriving DecidableEq

namespace Place

/-- Normalised real-valued absolute value attached to a place.

Reuses `Rat.AbsoluteValue.real` at infinity and `Rat.AbsoluteValue.padic`
at a finite prime. `Rat.AbsoluteValue.padic` takes `[Fact p.Prime]`,
so the proof in `prime` is turned into a local `Fact` dictionary. -/
noncomputable def absoluteValue : Place → AbsoluteValue ℚ ℝ
  | .infinite => Rat.AbsoluteValue.real
  | .finite prime =>
    haveI : Fact prime.1.Prime := ⟨prime.2⟩
    Rat.AbsoluteValue.padic prime.1

/-- Bundled carrier together with the `NormedField` / `CompleteSpace`
instances needed for the completed field `ℚ_v`.

Using a bundle avoids a direct dependent family `Place → Type` returning
`Padic p`, which loses the local `Fact` dictionary and causes kernel
declaration mismatches in projected instances. Instance-valued fields use
bracket syntax so the bundle itself carries the instances. -/
structure CompletedFieldBundle where
  carrier : Type
  [normedField : NormedField carrier]
  [completeSpace : CompleteSpace carrier]

instance : CoeSort CompletedFieldBundle Type where
  coe B := B.carrier

/-- Bundle selection by place. Exactly `ℝ` at infinity and `Padic p` at
a prime. `noncomputable abbrev` so reduction exposes standard real and
`p`-adic structures. -/
noncomputable abbrev bundle : Place → CompletedFieldBundle
  | .infinite => ⟨ℝ⟩
  | .finite prime =>
    haveI : Fact prime.1.Prime := ⟨prime.2⟩
    ⟨Padic prime.1⟩

/-- The completed field `ℚ_v` attached to a place `v`. Coerced from the
selected bundle. -/
noncomputable abbrev CompletedField (v : Place) : Type :=
  (bundle v : Type)

noncomputable instance (v : Place) : NormedField (CompletedField v) :=
  (bundle v).normedField

instance (v : Place) : CompleteSpace (CompletedField v) :=
  (bundle v).completeSpace

theorem completedField_infinite :
    CompletedField .infinite = ℝ :=
  rfl

theorem completedField_finite (prime : Nat.Primes) :
    letI : Fact prime.1.Prime := ⟨prime.2⟩
    CompletedField (.finite prime) = Padic prime.1 :=
  rfl

/-- Canonical ring embedding `ℚ →+* ℚ_v`.

At infinity this is `Rat.castHom ℝ`; at a finite prime it is
`Rat.castHom (Padic p)` under the local `Fact p.Prime` instance. -/
noncomputable def embedding : (v : Place) → ℚ →+* CompletedField v
  | .infinite => Rat.castHom ℝ
  | .finite prime =>
    haveI : Fact prime.1.Prime := ⟨prime.2⟩
    Rat.castHom (Padic prime.1)

/-- Evaluation at infinity. -/
theorem absoluteValue_infinite_apply (q : ℚ) :
    absoluteValue .infinite q = |(q : ℝ)| := by
  simp [absoluteValue, Rat.AbsoluteValue.real]

/-- Evaluation at a finite prime. -/
theorem absoluteValue_finite_apply (prime : Nat.Primes) (q : ℚ) :
    let _ : Fact prime.1.Prime := ⟨prime.2⟩
    absoluteValue (.finite prime) q = Rat.AbsoluteValue.padic prime.1 q :=
  rfl

/-- The embedding norm is the selected absolute value:

`‖embedding v q‖ = v.absoluteValue q`.

At infinity this follows by unfolding the selected embedding and absolute
value with `Rat.AbsoluteValue.real_eq_abs` and closing the resulting
`|(q : ℝ)| = ↑|q|` with `Rat.cast_abs` in the reverse direction;
`p`-adically it is `Padic.eq_padicNorm`. -/
theorem embedding_norm_eq_absoluteValue (v : Place) (q : ℚ) :
    ‖embedding v q‖ = v.absoluteValue q := by
  cases v with
  | infinite =>
    simp only [embedding, absoluteValue, Rat.AbsoluteValue.real_eq_abs]
    change |(q : ℝ)| = (↑|q| : ℝ)
    exact (Rat.cast_abs q).symm
  | finite prime =>
    let _ : Fact prime.1.Prime := ⟨prime.2⟩
    simp only [embedding, absoluteValue, Rat.AbsoluteValue.padic_eq_padicNorm]
    change ‖(q : Padic prime.1)‖ = (padicNorm prime.1 q : ℝ)
    exact Padic.eq_padicNorm q

/-- The image of `ℚ` is dense in each completed field `ℚ_v`.

Uses `Rat.denseRange_cast (𝕜 := ℝ)` at infinity and
`Padic.denseRange_ratCast p` under the local `Fact` at finite primes. -/
theorem denseRange_embedding (v : Place) :
    DenseRange (embedding v) := by
  cases v with
  | infinite =>
    simpa [embedding] using (Rat.denseRange_cast (𝕜 := ℝ))
  | finite prime =>
    let _ : Fact prime.1.Prime := ⟨prime.2⟩
    have h := Padic.denseRange_ratCast prime.1
    simpa [embedding] using h

/-- Translation of `Rat.AbsoluteValue.equiv_real_or_padic` into the
uniform place index.

`Rat.AbsoluteValue.equiv_real_or_padic` takes `f.IsNontrivial` and
concludes `f ≈ real ∨ ∃! p, ∃ (_ : Fact p.Prime), f ≈ padic p`;
this is repackaged as `∃ v : Place, f ≈ v.absoluteValue`, matching the
conclusion notation of Ostrowski directly. -/
theorem exists_place_equiv (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    ∃ v : Place, f ≈ v.absoluteValue := by
  have h := Rat.AbsoluteValue.equiv_real_or_padic f hf
  rcases h with hreal | ⟨p, ⟨hp, h⟩, _⟩
  · exact ⟨.infinite, by simpa [absoluteValue] using hreal⟩
  · exact ⟨.finite ⟨p, hp.out⟩, by
      let _ := hp
      simpa [absoluteValue] using h⟩

/-- Uniqueness of the representing rational place.

Preserves the unique-prime payload of `Rat.AbsoluteValue.equiv_real_or_padic`;
the opposite constructor is excluded via `Rat.AbsoluteValue.not_real_isEquiv_padic`
and equivalence symmetry/transitivity. -/
theorem exists_unique_place_equiv (f : AbsoluteValue ℚ ℝ) (hf : f.IsNontrivial) :
    ∃! v : Place, f ≈ v.absoluteValue := by
  have hex := Rat.AbsoluteValue.equiv_real_or_padic f hf
  rcases hex with hreal | ⟨p, ⟨hp, hpadic⟩, huniq⟩
  · refine ⟨.infinite, by simpa [absoluteValue] using hreal, ?_⟩
    intro w hw
    cases w with
    | infinite => rfl
    | finite prime =>
      let _ : Fact prime.1.Prime := ⟨prime.2⟩
      have hq : f ≈ Rat.AbsoluteValue.padic prime.1 := by
        simpa [absoluteValue] using hw
      have h : Rat.AbsoluteValue.real ≈ Rat.AbsoluteValue.padic prime.1 :=
        hreal.symm.trans hq
      exact absurd h (Rat.AbsoluteValue.not_real_isEquiv_padic (p := prime.1))
  · refine ⟨.finite ⟨p, hp.out⟩, by let _ := hp; simpa [absoluteValue] using hpadic, ?_⟩
    intro w hw
    cases w with
    | infinite =>
      have hreal' : f ≈ Rat.AbsoluteValue.real := by
        simpa [absoluteValue] using hw
      let _ := hp
      have h : Rat.AbsoluteValue.real ≈ Rat.AbsoluteValue.padic p :=
        hreal'.symm.trans hpadic
      exact absurd h (Rat.AbsoluteValue.not_real_isEquiv_padic (p := p))
    | finite prime =>
      let _ : Fact prime.1.Prime := ⟨prime.2⟩
      have hq : f ≈ Rat.AbsoluteValue.padic prime.1 := by
        simpa [absoluteValue] using hw
      have hq' : ∃ _ : Fact prime.1.Prime, f ≈ Rat.AbsoluteValue.padic prime.1 :=
        ⟨inferInstance, hq⟩
      have heq : prime.1 = p := huniq prime.1 hq'
      have hprime_eq : prime = ⟨p, hp.out⟩ := Subtype.ext heq
      rw [hprime_eq]

/-- Canonical ring hom from `WithAbs v.absoluteValue` into `v.CompletedField`.

`WithAbs.equiv` identifies the elements of the source with `ℚ`, allowing
`embedding v` to serve as the underlying hom and as the bridge for the norm
identity. -/
noncomputable def withAbsEmbedding (v : Place) :
    WithAbs (v.absoluteValue) →+* CompletedField v :=
  (embedding v).comp (WithAbs.equiv (v.absoluteValue)).toRingHom

/-- The `WithAbs` embedding is an isometry.

Uses `WithAbs.norm_eq_apply_ofAbs` to rewrite the `WithAbs` norm to the
absolute value, `embedding_norm_eq_absoluteValue` for the target norm,
and `AddMonoidHomClass.isometry_of_norm`. -/
theorem withAbsEmbedding_isometry (v : Place) :
    Isometry (withAbsEmbedding v) := by
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change ‖embedding v x.ofAbs‖ = ‖x‖
  rw [embedding_norm_eq_absoluteValue, WithAbs.norm_eq_apply_ofAbs]

/-- The `WithAbs` embedding has dense range, inherited from
`denseRange_embedding` via the bijective `WithAbs.equiv`. -/
theorem denseRange_withAbsEmbedding (v : Place) :
    DenseRange (withAbsEmbedding v) := by
  change Dense (Set.range ((embedding v) ∘ (WithAbs.equiv (v.absoluteValue))))
  rw [(WithAbs.equiv (v.absoluteValue)).surjective.range_comp]
  exact denseRange_embedding v

end Place

end Rat
