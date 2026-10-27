import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.TorsionSheaves
open AlgebraicGeometry CategoryTheory Opposite AlgebraicGeometry.TorsionSheaf


namespace AlgebraicGeometry.TorsionSheaf

/--
[isTorsionSection_iff_mem_torsion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionSheaves.lean)
-/
@[path]
lemma isTorsionSection_iff_mem_torsion
  {X : Scheme.{u}}
  [IsIntegral X]
  {F : X.Modules}
  {U : X.Opens}
  [Nonempty U]
  {s : (Scheme.Modules.presheaf F).obj (.op U)} :
-- imply
  IsTorsionSection F U s ↔ s ∈ Submodule.torsion (X.presheaf.obj (.op U)) ((Scheme.Modules.presheaf F).obj (.op U)) := by
-- proof
  constructor
  · rintro ⟨r, hr, hrs⟩
    exact ⟨⟨r, mem_nonZeroDivisors_iff_ne_zero.mpr hr⟩, hrs⟩
  · rintro ⟨⟨r, hr⟩, hrs⟩
    exact ⟨r, mem_nonZeroDivisors_iff_ne_zero.mp hr, hrs⟩

end AlgebraicGeometry.TorsionSheaf

namespace AlgebraicGeometry.TorsionSheaf

/--
[mem_torsionSections_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionSheaves.lean)
-/
@[path]
lemma mem_torsionSections_iff
  {X : Scheme.{u}}
  [IsIntegral X]
  {F : X.Modules}
  {U : X.Opens}
  [Nonempty U]
  {s : (Scheme.Modules.presheaf F).obj (.op U)} :
-- imply
  s ∈ torsionSections F U ↔ IsTorsionSection F U s :=
-- proof
  (isTorsionSection_iff_mem_torsion F U s).symm

end AlgebraicGeometry.TorsionSheaf

namespace AlgebraicGeometry.TorsionSheaf

/--
[isTorsionFreeSheaf_iff_torsionSections_eq_bot](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TorsionSheaves.lean)
-/
@[path]
lemma isTorsionFreeSheaf_iff_torsionSections_eq_bot
  {X : Scheme.{u}}
  [IsIntegral X]
  {F : X.Modules} :
-- imply
  IsTorsionFreeSheaf F ↔ ∀ (U : X.Opens) [Nonempty U], torsionSections F U = ⊥ := by
-- proof
  constructor
  · intro hF U _
    ext s
    simp only [mem_torsionSections_iff, Submodule.mem_bot]
    exact ⟨hF U s, fun h => by subst h; exact ⟨1, one_ne_zero, smul_zero 1⟩⟩
  · intro hF U _ s hs
    rw [← Submodule.mem_bot (R := X.presheaf.obj (.op U)),
      ← hF U, mem_torsionSections_iff]
    exact hs
/-- Torsion subsheaf (Def 39, Lec 22): on a Noetherian integral scheme, for
any sheaf of `O_X`-modules `F` there exists a subsheaf `T ↪ F` whose sections
over any nonempty open are exactly the torsion sections of `F`. -/

end AlgebraicGeometry.TorsionSheaf


-- created on 2026-10-23
