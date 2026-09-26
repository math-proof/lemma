import sympy.stats.markov_samples
import sympy.Basic
import Lemma.Iterates.Measurable.of.AdaptedOnSamplePath
import Lemma.Iterates.AdaptedOnSamplePath.of.IteratesOfResidual
open MeasureTheory Iterates


@[main]
private lemma main
  {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S] [MeasurableSpace S] [MeasurableSingletonClass S]
  {d : ℕ}
  {sk : Skeleton S d}
  {i m : ℕ}
  {g : (ℕ → S × S) → S × S}
-- given
  (h₀ : i ≤ m)
  (h₁ : Measurable[Filtration.piLE m] g) :
-- imply
  Measurable[Filtration.piLE m] (fun ω => sk.G (sk.x i ω) (g ω)) := by
-- proof
  have hx := (Measurable.of.AdaptedOnSamplePath (AdaptedOnSamplePath.of.IteratesOfResidual sk.hx) i).mono (Filtration.piLE.mono h₀) le_rfl
  exact (sk.hFm.comp (hx.prodMk h₁)).sub hx


-- created on 2026-09-26