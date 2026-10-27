import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.LieGroups.code.JantzenFiltration.Part2
open Classical


/--
[VermaJantzenFiltration.level_one_ne_top](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/JantzenFiltration.lean)
-/
@[path]
private lemma VermaJantzenFiltration.level_one_ne_top
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {hVM : IsVermaModule Δ M wt}
  {filt : VermaJantzenFiltration R 𝔤 M wt hVM} :
-- imply
  filt.level 1 ≠ ⊤ :=
-- proof
  filt.level_one_is_maximal.1

/--
[VermaJantzenFiltration.level_one_max](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/JantzenFiltration.lean)
-/
@[path]
private lemma VermaJantzenFiltration.level_one_max
  {R : Type*}
  [CommRing R]
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {hVM : IsVermaModule Δ M wt}
  {filt : VermaJantzenFiltration R 𝔤 M wt hVM}
  {N : LieSubmodule R 𝔤 M}
-- given
  (hN : N ≠ ⊤) :
-- imply
  N ≤ filt.level 1 :=
-- proof
  filt.level_one_is_maximal.2 N hN


-- created on 2026-10-23
-- updated on 2026-10-26
