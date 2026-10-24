import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GroupCohomology_TateCohomology
import Lemma.Definitions.Def_GroupCohomology_TateSeam
import Lemma.Definitions.Def_GroupCohomology_TateShiftMaps
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_tateMap_id](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_tateMap_id.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G] [Fintype G]
  {A : Rep.{u} k G}
  {n : ℤ} :
-- imply
  Rep.tateMap (𝟙 A) n = 𝟙 (A.tateCohomology n) := by
-- proof
  match n with
  | Int.ofNat (m + 1) => exact groupCohomology.map_id (m + 1)
  | Int.ofNat 0 =>
    show ModuleCat.ofHom (Rep.tateH0Map (𝟙 A)) = _
    rw [Rep.tateH0Map_id]
    rfl
  | Int.negSucc 0 =>
    show ModuleCat.ofHom (Rep.tateHneg1Map (𝟙 A)) = _
    rw [Rep.tateHneg1Map_id]
    rfl
  | Int.negSucc (m + 1) => exact groupHomology.map_id (m + 1)


-- created on 2026-10-23
