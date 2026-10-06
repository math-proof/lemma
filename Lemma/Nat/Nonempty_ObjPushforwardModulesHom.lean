import Mathlib
import sympy.Basic

open CategoryTheory AlgebraicGeometry

/--
[AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pushforward_hom_comp_iso.lean)
-/

noncomputable def pushEquiv
  {X Y : Scheme.{u}}
  (φ : X ≅ Y)
  : X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward φ.hom) (Scheme.Modules.pushforward φ.inv)
    ((Scheme.Modules.pushforwardId X).symm ≪≫ Scheme.Modules.pushforwardCongr φ.hom_inv_id.symm ≪≫
      (Scheme.Modules.pushforwardComp φ.hom φ.inv).symm)
    (Scheme.Modules.pushforwardComp φ.inv φ.hom ≪≫ Scheme.Modules.pushforwardCongr φ.inv_hom_id ≪≫
      Scheme.Modules.pushforwardId Y)

noncomputable def pullbackIsoPushforwardInv
    {X Y : Scheme.{u}}
    (φ : X ≅ Y)
    :
    Scheme.Modules.pullback φ.hom ≅ Scheme.Modules.pushforward φ.inv :=
  (Scheme.Modules.pullbackPushforwardAdjunction φ.hom).leftAdjointUniq (pushEquiv φ).symm.toAdjunction
@[main]
private lemma main
  {X Y Z : Scheme.{u}}
  {e : X ≅ Y}
  {f : Y ⟶ Z}
  {F : X.Modules} :
-- imply
  Nonempty ((Scheme.Modules.pushforward (e.hom ≫ f)).obj F ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback e.inv).obj F)) :=
-- proof
  ⟨(Scheme.Modules.pushforwardComp e.hom f).symm.app F ≪≫
    (Scheme.Modules.pushforward f).mapIso ((pullbackIsoPushforwardInv e.symm).app F).symm⟩


-- created on 2026-10-05
