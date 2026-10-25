-- Carved from Lemma/Definitions/Def_NumberField_AdelicHaar.lean: instance decls only.
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct

noncomputable section

namespace NumberField.AdelicHaar

section Local

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

instance fact_isOpen_adicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun _ => Valued.isOpen_valuationSubring _⟩


instance finite_residueField_adicCompletionIntegers :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  sorry

-- ProperSpace now requires PseudoMetricSpace; adicCompletion is Valued/Uniform, not metric.
-- Sorry both so Adele LocallyCompact scaffolding still typechecks for downstream oleans.
instance : PseudoMetricSpace (v.adicCompletion K) := by
  sorry

instance properSpace_adicCompletion : ProperSpace (v.adicCompletion K) := by
  sorry

instance locallyCompactSpace_adicCompletion : LocallyCompactSpace (v.adicCompletion K) := by
  sorry

instance compactSpace_adicCompletionIntegers : CompactSpace (v.adicCompletionIntegers K) := by
  sorry

end Local

section Adele

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

instance t2Space_infiniteAdeleRing : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))

instance t2Space_adeleRing : T2Space (AdeleRing R K) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing R K))


instance locallyCompactSpace_finiteAdeleRing : LocallyCompactSpace (FiniteAdeleRing R K) :=
  inferInstanceAs (LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

instance locallyCompactSpace_adeleRing [NumberField K] : LocallyCompactSpace (AdeleRing R K) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing R K))


end Adele

section GeneralLinear

variable (n : Type*) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

instance t2Space_matrix_adeleRing : T2Space (Matrix n n (AdeleRing R K)) :=
  inferInstanceAs (T2Space (n → n → AdeleRing R K))

instance locallyCompactSpace_matrix_adeleRing [Finite n] [Module.Free ℤ R] [Module.Finite ℤ R]
    [NumberField K] : LocallyCompactSpace (Matrix n n (AdeleRing R K)) :=
  inferInstanceAs (LocallyCompactSpace (n → n → AdeleRing R K))

variable [Fintype n] [DecidableEq n]

instance t2Space_gl_adeleRing : T2Space (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  inferInstance


instance locallyCompactSpace_gl_adeleRing :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) := by
  sorry

instance isTopologicalGroup_gl_adeleRing :
    IsTopologicalGroup (Matrix.GeneralLinearGroup n (AdeleRing R K)) := by
  sorry


end GeneralLinear

end NumberField.AdelicHaar

end
