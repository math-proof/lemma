import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.BGGResolution


/--
[projective_implies_ext1_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/BGGResolution.lean)
-/
@[path]
private lemma projective_implies_ext1_vanishes
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {X : Type uCatO}
  [AddCommGroup X]
  [Module R X]
  [LieRingModule 𝔤 X]
  [LieModule R 𝔤 X]
  {Y : Type uCatO}
  [AddCommGroup Y]
  [Module R Y]
  [LieRingModule 𝔤 Y]
  [LieModule R 𝔤 Y]
-- given
  (hXO : IsCategoryO Δ rd X)
  (hXproj : IsProjectiveInO rd X hXO)
  (hYO : IsCategoryO Δ rd Y) :
-- imply
  ExtVanishes_CategoryO rd 1 X hXO Y hYO := by
-- proof
  intro E _ _ _ _ hEO ι _hι p hp _hexact
  exact hXproj E hEO X hXO p hp (LieModuleHom.id : X →ₗ⁅R, 𝔤⁆ X)


-- created on 2026-10-23
-- updated on 2026-10-26
