module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.NumberTheory.RamificationInertia.Inertia
public import Mathlib.RingTheory.Valuation.Discrete.Basic
public import Mathlib.Topology.Path
public import Mathlib.Algebra.Group.Int.TypeTags
public import Mathlib.RingTheory.Valuation.Discrete.RankOne
@[expose] public section

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
