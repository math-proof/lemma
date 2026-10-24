import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.Lec8IntersectionCodim
open Ideal


/--
[height_minPrime_sup_le_spanRank_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8IntersectionCodim.lean)
-/
@[path]
lemma height_minPrime_sup_le_spanRank_add
  [CommRing R]
  [IsNoetherianRing R]
  {I J : Ideal R}
  {P : Ideal R}
-- given
  (hP : P ∈ (I ⊔ J).minimalPrimes) :
-- imply
  P.height ≤ Cardinal.toENat (Submodule.spanRank I) + Cardinal.toENat (Submodule.spanRank J) :=
-- proof
  calc P.height
    ≤ Cardinal.toENat (Submodule.spanRank (I ⊔ J)) :=
      Ideal.height_le_spanRank_toENat_of_mem_minimal_primes _ _ hP
    _ ≤ Cardinal.toENat (Submodule.spanRank I + Submodule.spanRank J) :=
      OrderHomClass.mono Cardinal.toENat Submodule.spanRank_sup_le_sum_spanRank
    _ = Cardinal.toENat (Submodule.spanRank I) + Cardinal.toENat (Submodule.spanRank J) :=
      map_add Cardinal.toENat _ _

/--
[height_minPrime_sup_le_spanFinrank_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec8IntersectionCodim.lean)
-/
@[path]
lemma height_minPrime_sup_le_spanFinrank_add
  [CommRing R]
  [IsNoetherianRing R]
  {I J : Ideal R}
  {P : Ideal R}
-- given
  (hP : P ∈ (I ⊔ J).minimalPrimes) :
-- imply
  P.height ≤ ↑(Submodule.spanFinrank I + Submodule.spanFinrank J) := by
-- proof
  have h := height_minPrime_sup_le_spanRank_add I J P hP
  have hfgI : I.FG := IsNoetherian.noetherian I
  have hfgJ : J.FG := IsNoetherian.noetherian J
  have hltI := Submodule.spanRank_finite_iff_fg.mpr hfgI
  have hltJ := Submodule.spanRank_finite_iff_fg.mpr hfgJ
  obtain ⟨nI, hI⟩ := Cardinal.lt_aleph0.mp hltI
  obtain ⟨nJ, hJ⟩ := Cardinal.lt_aleph0.mp hltJ
  simp only [Submodule.spanFinrank, hI, hJ, Cardinal.toNat_natCast] at h ⊢
  simpa [Cardinal.toENat_nat] using h


-- created on 2026-10-23
