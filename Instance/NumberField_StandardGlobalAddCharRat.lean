-- Carved from Lemma/Definitions/Def_NumberField_StandardGlobalAddCharRat.lean: instance decls only.
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Analysis.Normed.Ring.Ultra
import Lemma.AutomorphicForm.WhittakerCoefficient

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
