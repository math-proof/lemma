-- Carved from Lemma/Definitions/Def_NumberField_StandardGlobalAddCharRat.lean: instance decls only.

module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.NumberTheory.Padics.HeightOneSpectrum
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.Analysis.Normed.Ring.Ultra

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace NumberField.StandardAddChar

open scoped Real

variable {p : ℕ} [Fact p.Prime]

section PlaceChar

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

variable (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ))

end PlaceChar


section Reciprocity

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

end Reciprocity


section FullChar

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

end FullChar


end NumberField.StandardAddChar

end
