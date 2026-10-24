import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.NumberField.RayClass.WeakApproximation
open scoped nonZeroDivisors
open NumberField
open Modulus


namespace NumberField.Modulus

/--
[exists_ne_zero_with_valuation_one_and_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/WeakApproximation.lean)
-/
@[path]
lemma exists_ne_zero_with_valuation_one_and_sign
  [Field F] [Finite ι] [Field K] [NumberField K]
  {m : Modulus K}
-- given
  (pos : {w : RealPlace K // w ∈ m.infinitePart} → Prop) :
-- imply
  ∃ x : K, x ≠ 0 ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    finiteSupported m v → v.valuation K x = 1) ∧
    ∀ (w : RealPlace K) (hw : w ∈ m.infinitePart),
    (pos ⟨w, hw⟩ → 0 < InfinitePlace.embedding_of_isReal w.property x) ∧
    (¬ pos ⟨w, hw⟩ → InfinitePlace.embedding_of_isReal w.property x < 0) := by
-- proof
  obtain ⟨x, hxne, hval, hsign⟩ := exists_ne_zero_with_target_and_sign m 1 pos
    one_ne_zero (fun _ _ => map_one _)
  exact ⟨x, hxne, fun v hv => (hval v hv).1, hsign⟩

end NumberField.Modulus

/--
[exists_ne_zero_with_target_and_sign](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/RayClass/WeakApproximation.lean)
-/
@[path]
private lemma exists_ne_zero_with_target_and_sign_eq
  [Field F] [Finite ι] [Field K] [NumberField K]
  {m : Modulus K}
  {a : K}
-- given
  (pos : {w : RealPlace K // w ∈ m.infinitePart} → Prop)
  (ha0 : a ≠ 0)
  (haval : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K), finiteSupported m v → v.valuation K a = 1) :
-- imply
  ∃ x : K, x ≠ 0 ∧
    (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 K),
    finiteSupported m v →
    v.valuation K x = 1 ∧
    v.valuation K (x - a) ≤ WithZero.exp (-(finiteExponent m v))) ∧
    ∀ (w : RealPlace K) (hw : w ∈ m.infinitePart),
    (pos ⟨w, hw⟩ → 0 < InfinitePlace.embedding_of_isReal w.property x) ∧
    (¬ pos ⟨w, hw⟩ → InfinitePlace.embedding_of_isReal w.property x < 0) := by
-- proof
  apply NumberField.Modulus.exists_ne_zero_with_target_and_sign m a pos ha0 haval


-- created on 2026-10-20
-- updated on 2026-10-23
