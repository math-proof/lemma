import Mathlib
import sympy.Basic


/--
[CohCarrier_index_comap_unitsMap](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CohCarrier_index_comap_unitsMap.lean)
-/
@[path]
private lemma main
  {M M' : ℕ} [NeZero M']
  {H₀ : Subgroup (ZMod M)ˣ}
-- given
  (hMM' : M ∣ M') :
-- imply
  (H₀.comap (ZMod.unitsMap hMM')).index = H₀.index :=
-- proof
  Subgroup.index_comap_of_surjective _ (ZMod.unitsMap_surjective hMM')


-- created on 2026-10-03
