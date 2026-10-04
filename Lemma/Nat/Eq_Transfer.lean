import Mathlib
import sympy.Basic


/--
[MonoidHom_map_transfer_eq_transfer_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_MonoidHom_map_transfer_eq_transfer_comp.lean)
-/
@[main]
private lemma main
  [Group G]
  {H : Subgroup G} [H.FiniteIndex]
  {A B : Type*} [CommGroup A] [CommGroup B]
  {ϕ : ↥H →* A}
  {f : A →* B}
  {g : G} :
-- imply
  f (MonoidHom.transfer ϕ g) = MonoidHom.transfer (f.comp ϕ) g := by
-- proof
  classical
  rw [MonoidHom.transfer_def ϕ (default : H.LeftTransversal) g,
    MonoidHom.transfer_def (f.comp ϕ) (default : H.LeftTransversal) g]
  unfold Subgroup.leftTransversals.diff
  simp only [map_prod, MonoidHom.comp_apply]


-- created on 2026-10-03
