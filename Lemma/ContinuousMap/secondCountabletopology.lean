import Mathlib
import Initialize.Tactic.Attr.Basic
open IsModuleTopology Topology


@[path]
private lemma main
  [CommRing R]
  [TopologicalSpace R]
  [IsTopologicalRing R]
  [SecondCountableTopology R]
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [TopologicalSpace M]
  [IsModuleTopology R M] :
-- imply
  SecondCountableTopology M := by
-- proof
  obtain ⟨n, φ, hφ⟩ := Module.Finite.exists_fin' R M
  apply IsOpenQuotientMap.secondCountableTopology
    (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
      (isQuotientMap_of_surjective hφ))


-- created on 2026-11-13
