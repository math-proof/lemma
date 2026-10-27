import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GroupCohomology.ContinuousH1
import Lemma.Int.P2MUtil
open CategoryTheory groupCohomology
open Int


namespace Definitions
end Definitions

/--
[groupCohomology_map_apply_mem_continuousH1_comp](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_map_apply_mem_continuousH1_comp.lean)
-/
@[path]
private lemma main
  {k G H : Type u} [CommRing k] [Group G] [Group H]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {loc : H →* G}
  {M : Rep.{u} k G}
  {x : H1 M}
-- given
  (hx : x ∈ continuousH1 r M) :
-- imply
  (map loc (𝟙 (Rep.res loc M)) 1).hom x ∈ continuousH1 (r.comp loc) (Rep.res loc M) := by
-- proof
  obtain ⟨c, hc, rfl⟩ := (mem_continuousH1_iff r M x).1 hx
  have hcomp : (map loc (𝟙 (Rep.res loc M)) 1).hom ((H1π M).hom c) =
    (H1π (Rep.res loc M)).hom (mapCocycles₁ loc (𝟙 (Rep.res loc M)) c) :=
    H1π_comp_map_apply loc (𝟙 (Rep.res loc M)) c
  rw [hcomp]
  refine H1π_mem_continuousH1 (r.comp loc) (Rep.res loc M) ?_
  obtain ⟨F, hF, hc⟩ := hc
  refine ⟨F, hF, fun h s hs => ?_⟩
  show c (loc (h * s)) = c (loc h)
  rw [map_mul]
  exact hc (loc h) (loc s) hs


-- created on 2026-10-24
