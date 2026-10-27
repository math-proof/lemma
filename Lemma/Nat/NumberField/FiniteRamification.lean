import Mathlib
import Initialize.Tactic.Attr.Basic
open IsDedekindDomain


namespace NumberField

/--
[finite_ramified_primes](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/NumberField/FiniteRamification.lean)
-/
@[path]
lemma finite_ramified_primes
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
-- imply
  {p : HeightOneSpectrum (NumberField.RingOfIntegers K) |
      ¬ Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) p.asIdeal}.Finite := by
-- proof
  classical
  let _ : Algebra
    (FractionRing (NumberField.RingOfIntegers K))
    (FractionRing (NumberField.RingOfIntegers L)) :=
    FractionRing.liftAlgebra _ _
  let f := fun P : HeightOneSpectrum (NumberField.RingOfIntegers L) =>
    P.under (NumberField.RingOfIntegers K)
  have hfinite : {P : HeightOneSpectrum (NumberField.RingOfIntegers L) |
    P.asIdeal ∣ differentIdeal (NumberField.RingOfIntegers K)
      (NumberField.RingOfIntegers L)}.Finite :=
    Ideal.finite_factors differentIdeal_ne_bot
  apply (hfinite.image f).subset
  intro p hp
  rw [Set.mem_image]
  change ¬ Algebra.IsUnramifiedIn (NumberField.RingOfIntegers L) p.asIdeal at hp
  simp only [Algebra.IsUnramifiedIn, not_forall] at hp
  obtain ⟨P, hPprime, hPover, hPram⟩ := hp
  let _ : P.IsPrime := hPprime
  let _ : P.LiesOver p.asIdeal := hPover
  let Q : HeightOneSpectrum (NumberField.RingOfIntegers L) :=
    ⟨P, hPprime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot P⟩
  refine ⟨Q, ?_, ?_⟩
  · exact (dvd_differentIdeal_iff
    (A := NumberField.RingOfIntegers K)
    (B := NumberField.RingOfIntegers L)).2 hPram
  · apply HeightOneSpectrum.ext
    exact Ideal.LiesOver.over.symm

end NumberField


-- created on 2026-10-20
-- updated on 2026-10-26
