import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GroupCohomology_TateCohomology
import Lemma.Definitions.Def_GroupCohomology_TateSeam
import Lemma.Definitions.Def_GroupCohomology_TateShiftMaps
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_tateMap_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_tateMap_comp.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G] [Fintype G]
  {A B C : Rep.{u} k G}
  {φ : A ⟶ B}
  {ψ : B ⟶ C}
  {n : ℤ} :
-- imply
  Rep.tateMap (φ ≫ ψ) n = Rep.tateMap φ n ≫ Rep.tateMap ψ n := by
-- proof
  match n with
  | Int.ofNat (m + 1) => exact (groupCohomology.functor k G (m + 1)).map_comp φ ψ
  | Int.ofNat 0 =>
    show ModuleCat.ofHom (Rep.tateH0Map (φ ≫ ψ)) = ModuleCat.ofHom (Rep.tateH0Map φ) ≫ ModuleCat.ofHom (Rep.tateH0Map ψ)
    rw [Rep.tateH0Map_comp, ModuleCat.ofHom_comp]
  | Int.negSucc 0 =>
    show ModuleCat.ofHom (Rep.tateHneg1Map (φ ≫ ψ)) = ModuleCat.ofHom (Rep.tateHneg1Map φ) ≫ ModuleCat.ofHom (Rep.tateHneg1Map ψ)
    rw [Rep.tateHneg1Map_comp, ModuleCat.ofHom_comp]
  | Int.negSucc (m + 1) => exact (groupHomology.functor k G (m + 1)).map_comp φ ψ


-- created on 2026-10-23
