import Mathlib.Topology.Algebra.Valued.ValuationTopology
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.Valuation.Discrete.Basic
import Mathlib.Topology.Path
import Mathlib.Algebra.Group.Int.TypeTags
import Mathlib.RingTheory.Valuation.Discrete.RankOne
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 400000

section

namespace IsDedekindDomain.HeightOneSpectrum

open IsDedekindDomain


end IsDedekindDomain.HeightOneSpectrum

end

section

end

section

variable {F : Type*} [Field F]

end

section

namespace IsDedekindDomain.HeightOneSpectrum

section Multiplicative

open scoped WithZero

end Multiplicative

variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)


noncomputable abbrev completionIdeal : Ideal (v.adicCompletionIntegers K) :=
  IsLocalRing.maximalIdeal (adicCompletionIntegers K v)


namespace adicCompletion


end adicCompletion

end IsDedekindDomain.HeightOneSpectrum

end
