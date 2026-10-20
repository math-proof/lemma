import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Rat.Place
open Rat
open Place


/--
[completedField_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma completedField_infinite_eq
  :
-- imply
  CompletedField .infinite = ℝ := by
-- proof
  apply Rat.Place.completedField_infinite

/--
[completedField_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma completedField_finite_eq
  {prime : Nat.Primes} :
-- imply
  letI : Fact prime.1.Prime := by
-- proof
  apply Rat.Place.completedField_finite prime

/--
[absoluteValue_infinite_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma absoluteValue_infinite_apply_eq
  {q : ℚ} :
-- imply
  absoluteValue .infinite q = |(q : ℝ)| := by
-- proof
  apply Rat.Place.absoluteValue_infinite_apply q

/--
[absoluteValue_finite_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma absoluteValue_finite_apply_eq
  {prime : Nat.Primes}
  {q : ℚ} :
-- imply
  let _ : Fact prime.1.Prime := by
-- proof
  apply Rat.Place.absoluteValue_finite_apply prime q

/--
[embedding_norm_eq_absoluteValue](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma embedding_norm_eq_absoluteValue_eq
  {v : Place}
  {q : ℚ} :
-- imply
  ‖embedding v q‖ = v.absoluteValue q := by
-- proof
  apply Rat.Place.embedding_norm_eq_absoluteValue v q

/--
[denseRange_embedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma denseRange_embedding_eq
  {v : Place} :
-- imply
  DenseRange (embedding v) := by
-- proof
  apply Rat.Place.denseRange_embedding v

/--
[exists_place_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma exists_place_equiv_eq
  {f : AbsoluteValue ℚ ℝ}
-- given
  (hf : f.IsNontrivial) :
-- imply
  ∃ v : Place, f ≈ v.absoluteValue := by
-- proof
  apply Rat.Place.exists_place_equiv f hf

/--
[exists_unique_place_equiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma exists_unique_place_equiv_eq
  {f : AbsoluteValue ℚ ℝ}
-- given
  (hf : f.IsNontrivial) :
-- imply
  ∃! v : Place, f ≈ v.absoluteValue := by
-- proof
  apply Rat.Place.exists_unique_place_equiv f hf

/--
[withAbsEmbedding_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma withAbsEmbedding_isometry_eq
  {v : Place} :
-- imply
  Isometry (withAbsEmbedding v) := by
-- proof
  apply Rat.Place.withAbsEmbedding_isometry v

/--
[denseRange_withAbsEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Rat/Place.lean)
-/
@[path]
private lemma denseRange_withAbsEmbedding_eq
  {v : Place} :
-- imply
  DenseRange (withAbsEmbedding v) := by
-- proof
  apply Rat.Place.denseRange_withAbsEmbedding v


-- created on 2026-10-20
