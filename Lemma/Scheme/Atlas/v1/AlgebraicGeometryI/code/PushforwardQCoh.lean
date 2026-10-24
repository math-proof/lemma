import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.PushforwardQCoh
open AlgebraicGeometry CategoryTheory TopologicalSpace Lemma24


namespace Lemma24

/--
[affineOpens_coversTop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PushforwardQCoh.lean)
-/
@[path]
lemma affineOpens_coversTop
  {Y : Scheme.{u}} :
-- imply
  (Opens.grothendieckTopology Y).CoversTop (fun (U : Y.affineOpens) => (U : TopologicalSpace.Opens Y)) := by
-- proof
  intro V x hx
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.2
  exact ⟨W, homOfLE hWV, ⟨⟨W, hW⟩, ⟨𝟙 _⟩⟩, hxW⟩
set_option maxHeartbeats 800000 in
/-- Lemma 24 (global): the pushforward `f_*F` along a morphism of schemes `f : X → Y`
of a quasicoherent `F` on `X` is again quasicoherent. This is obtained by gluing the
local case over the affine cover of `Y`. -/
end Lemma24



-- created on 2026-10-23
