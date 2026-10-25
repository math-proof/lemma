-- Carved from Lemma/Definitions/Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace.lean: instance decls only.
import Mathlib
import Def.Mathlib_Topology_Algebra_ContinuousMonoidHom
import Lemma.Set.IsOpenUnits.of.IsOpenSet
import Lemma.Topology.Algebra.RestrictedProduct.Equiv
import Lemma.Filter.CountableSetsCofinite
import Lemma.Filter.SecondCountableBases
import Lemma.Topology.Algebra.RestrictedProduct.TopologicalSpace

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
