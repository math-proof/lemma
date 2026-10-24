import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Rat.Place
open Rat
open Place


namespace Rat.Place

/--
[completedField_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma completedField_infinite
  :
-- imply
  CompletedField .infinite = ℝ :=
-- proof
  rfl

end Rat.Place

namespace Rat.Place

/--
[completedField_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma completedField_finite
  {prime : Nat.Primes} :
-- imply
  letI : Fact prime.1.Prime :=
-- proof
  rfl

end Rat.Place

namespace Rat.Place

/--
[absoluteValue_infinite_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma absoluteValue_infinite_apply
  {q : ℚ} :
-- imply
  absoluteValue .infinite q = |(q : ℝ)| := by
-- proof
  simp [absoluteValue, Rat.AbsoluteValue.real]

end Rat.Place

namespace Rat.Place

/--
[absoluteValue_finite_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma absoluteValue_finite_apply
  {prime : Nat.Primes}
  {q : ℚ} :
-- imply
  let _ : Fact prime.1.Prime :=
-- proof
  rfl

end Rat.Place

namespace Rat.Place

/--
[embedding_norm_eq_absoluteValue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma embedding_norm_eq_absoluteValue
  {v : Place}
  {q : ℚ} :
-- imply
  ‖embedding v q‖ = v.absoluteValue q := by
-- proof
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

end Rat.Place

namespace Rat.Place

/--
[denseRange_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma denseRange_embedding
  {v : Place} :
-- imply
  DenseRange (embedding v) := by
-- proof
  cases v with
  | infinite =>
    simpa [embedding] using (Rat.denseRange_cast (𝕜 := ℝ))
  | finite prime =>
    let _ : Fact prime.1.Prime := ⟨prime.2⟩
    have h := Padic.denseRange_ratCast prime.1
    simpa [embedding] using h

end Rat.Place

namespace Rat.Place

/--
[exists_place_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma exists_place_equiv
  {f : AbsoluteValue ℚ ℝ}
-- given
  (hf : f.IsNontrivial) :
-- imply
  ∃ v : Place, f ≈ v.absoluteValue := by
-- proof
  have h := Rat.AbsoluteValue.equiv_real_or_padic f hf
  obtain hreal | ⟨p, ⟨hp, h⟩, _⟩ := h
  · exact ⟨.infinite, by simpa [absoluteValue] using hreal⟩
  · exact ⟨.finite ⟨p, hp.out⟩, by
    let _ := hp
    simpa [absoluteValue] using h⟩

end Rat.Place

namespace Rat.Place

/--
[exists_unique_place_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma exists_unique_place_equiv
  {f : AbsoluteValue ℚ ℝ}
-- given
  (hf : f.IsNontrivial) :
-- imply
  ∃! v : Place, f ≈ v.absoluteValue := by
-- proof
  have hex := Rat.AbsoluteValue.equiv_real_or_padic f hf
  obtain hreal | ⟨p, ⟨hp, hpadic⟩, huniq⟩ := hex
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

end Rat.Place

namespace Rat.Place

/--
[withAbsEmbedding_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma withAbsEmbedding_isometry
  {v : Place} :
-- imply
  Isometry (withAbsEmbedding v) := by
-- proof
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  change ‖embedding v x.ofAbs‖ = ‖x‖
  rw [embedding_norm_eq_absoluteValue, WithAbs.norm_eq_apply_ofAbs]

end Rat.Place

namespace Rat.Place

/--
[denseRange_withAbsEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
lemma denseRange_withAbsEmbedding
  {v : Place} :
-- imply
  DenseRange (withAbsEmbedding v) := by
-- proof
  change Dense (Set.range ((embedding v) ∘ (WithAbs.equiv (v.absoluteValue))))
  rw [(WithAbs.equiv (v.absoluteValue)).surjective.range_comp]
  exact denseRange_embedding v

end Rat.Place


-- created on 2026-10-20
-- updated on 2026-10-23
