-- Carved from Lemma/Definitions/Def_NarrowRayClassGroup.lean: instance decls only.
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.ClassGroup
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
import Mathlib.GroupTheory.QuotientGroup.Finite
import Mathlib.Data.Fintype.Units
import Lemma.NarrowRayClassGroup.Main

open NumberField nonZeroDivisors IsDedekindDomain

noncomputable section

namespace Deep.NTSupply


section Finiteness

variable (K : Type*) [Field K] [NumberField K]

instance instNormalRayClassSubgroup (𝔣 : Ideal (𝓞 K)) : (rayClassSubgroup K 𝔣).Normal :=
  ⟨fun n hn g => by rwa [mul_comm g n, mul_inv_cancel_right]⟩

end Finiteness


end Deep.NTSupply
end
