/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/NumberField/AdeleLocallyCompact.lean -/


import sympy.atlas.NumberTheory.NumberField.AdeleLocallyCompact
import Lemma.Nat.NumberField.AdeleLocallyCompact
import Lemma.Int.DedekindDomain.AdicCompletionResidueField
import sympy.atlas.RingTheory.DedekindDomain.AdicCompletionResidueField


noncomputable section

open NumberField IsDedekindDomain

namespace HeightOneSpectrumTest

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- Kernel of the residue-field map starting at `𝓞 ℚ`. -/
example : RingHom.ker (v.completionResidueMap (K := ℚ)) = v.asIdeal :=
  v.ker_completionResidueMap

/-- Surjectivity onto the completion's residue field. -/
example (q : ↥(v.adicCompletionIntegers ℚ) ⧸
    IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers ℚ)) :
    ∃ a : 𝓞 ℚ, v.completionResidueMap (K := ℚ) a = q :=
  v.surjective_completionResidueMap (K := ℚ) q

/-- Residue-field equivalence. -/
example : (↥(v.adicCompletionIntegers ℚ) ⧸
    IsLocalRing.maximalIdeal ↥(v.adicCompletionIntegers ℚ)) ≃+* (𝓞 ℚ ⧸ v.asIdeal) :=
  v.completionResidueFieldEquiv

/-- Finite residue field of the local completion integers. -/
example : Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) :=
  HeightOneSpectrum.finite_residueField ℚ v

/-- Compactness of the local completion integers. -/
example : CompactSpace (Valued.integer (v.adicCompletion ℚ)) := inferInstance

/-- Adic completeness of the local completion integers. -/
example : IsAdicComplete
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ))
    (v.adicCompletionIntegers ℚ) := inferInstance

/-- Properness of the local completion. -/
example : ProperSpace (v.adicCompletion ℚ) := inferInstance

/-- Compactness bridge for the adic completion integers. -/
example : IsCompact (↑(v.adicCompletionIntegers ℚ) : Set (v.adicCompletion ℚ)) :=
  HeightOneSpectrum.isCompact_adicCompletionIntegers ℚ v

end HeightOneSpectrumTest

section TestRational

example : T2Space (InfiniteAdeleRing ℚ) := inferInstance

example : T2Space (FiniteAdeleRing (𝓞 ℚ) ℚ) := inferInstance

example : T2Space (AdeleRing (𝓞 ℚ) ℚ) := inferInstance

example : LocallyCompactSpace (FiniteAdeleRing (𝓞 ℚ) ℚ) := inferInstance

example : LocallyCompactSpace (AdeleRing (𝓞 ℚ) ℚ) := inferInstance

end TestRational

section TestGeneric

variable (K : Type*) [Field K] [NumberField K]

/-- Generic full-adele synthesis: `T2` and locally compact together. -/
example : T2Space (AdeleRing (𝓞 K) K) ∧ LocallyCompactSpace (AdeleRing (𝓞 K) K) :=
  ⟨inferInstance, inferInstance⟩

end TestGeneric
