-- Carved from Lemma/Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace.lean: instance decls only.
module

public import Mathlib
public import Def.Mathlib_Topology_Algebra_ContinuousMonoidHom
public import Theorem.Set.IsOpenUnits.of.IsOpenSet
public import Theorem.Filter.Algebra.RestrictedProduct.Equiv
public import Theorem.Filter.CountableSetsCofinite
public import Theorem.Filter.SecondCountableBases
public import Theorem.Filter.Algebra.RestrictedProduct.TopologicalSpace
@[expose] public section

section

open RestrictedProduct

variable {ι : Type*}
variable {ℱ : Filter ι}


open RestrictedProduct Filter in
instance RestrictedProduct.SecondCountableTopology_of_principal
    {ι : Type*} [Countable ι]
    (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
    (C : (i : ι) → Set (X i))
    [∀ i, SecondCountableTopology (X i)]
    {S : Set ι} :
    SecondCountableTopology (Πʳ i, [X i, C i]_[𝓟 S]) :=
  isEmbedding_coe_of_principal.secondCountableTopology


end
