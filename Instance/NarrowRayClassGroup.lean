module
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.ClassGroup
public import Mathlib.LinearAlgebra.FreeModule.IdealQuotient
public import Mathlib.GroupTheory.QuotientGroup.Finite
public import Mathlib.Data.Fintype.Units
public import Theorem.Ideal.Main
public import Def.Ideal_Main
open NumberField nonZeroDivisors IsDedekindDomain


public section

-- Carved from Lemma/Definitions/Def_NarrowRayClassGroup.lean: instance decls only.

noncomputable section

namespace Deep.NTSupply


section Finiteness

variable (K : Type*) [Field K] [NumberField K]

instance instNormalRayClassSubgroup (𝔣 : Ideal (𝓞 K)) : (rayClassSubgroup K 𝔣).Normal :=
  ⟨fun n hn g => by rwa [mul_comm g n, mul_inv_cancel_right]⟩

end Finiteness


end Deep.NTSupply
end
