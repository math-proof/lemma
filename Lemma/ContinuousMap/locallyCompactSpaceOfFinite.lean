import Mathlib
import Initialize.Tactic.Attr.Basic
open IsModuleTopology


@[path]
private lemma main
  [TopologicalSpace R]
  [Ring R]
  [IsTopologicalRing R]
  [AddCommGroup M]
  [Module R M]
  [TopologicalSpace M]
  [IsModuleTopology R M]
  [LocallyCompactSpace R]
  [Module.Finite R M] :
-- imply
  LocallyCompactSpace M := by
-- proof
  obtain ⟨n, φ, h⟩ := Module.Finite.exists_fin (R := R) (M := M)
  apply IsOpenQuotientMap.locallyCompactSpace
    (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
      (isQuotientMap_of_surjective
        (LinearMap.range_eq_top.mp (h ▸ Fintype.range_linearCombination R φ))))


-- created on 2026-11-13
