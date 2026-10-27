import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AlgebraicCurve.CurveModel
import Lemma.Int.P2MUtil
open CategoryTheory AlgebraicGeometry AlgebraicCurve


/--
[AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_CurveModel_place_eq_of_pointEquivPlace_symm_comp_eq.lean)
-/
@[path]
private lemma main
  {K : Type u} [Field K] [IsAlgClosed K]
  {L : Type v} [Field L] [Algebra K L]
  {𝔐 : AlgebraicCurve.CurveModel K L}
  {X B : Scheme.{u}}
  {πX : X ⟶ B}
  {s : Spec (CommRingCat.of K) ⟶ B}
  {e : 𝔐.C ⟶ CategoryTheory.Limits.pullback πX s}
  {P Q : Place K L}
-- given
  (he : IsIso e)
  (he_snd : e ≫ CategoryTheory.Limits.pullback.snd πX s = 𝔐.toBase)
  (h : (𝔐.pointEquivPlace.symm P).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s = (𝔐.pointEquivPlace.symm Q).1 ≫ e ≫ CategoryTheory.Limits.pullback.fst πX s) :
-- imply
  P = Q := by
  have h2 : (𝔐.pointEquivPlace.symm P).1 ≫ e = (𝔐.pointEquivPlace.symm Q).1 ≫ e := by
-- proof
    apply CategoryTheory.Limits.pullback.hom_ext
    · simpa only [Category.assoc] using h
    · rw [Category.assoc, he_snd, (𝔐.pointEquivPlace.symm P).2, Category.assoc, he_snd, (𝔐.pointEquivPlace.symm Q).2]
  have := he
  have h3 : (𝔐.pointEquivPlace.symm P).1 = (𝔐.pointEquivPlace.symm Q).1 := (cancel_mono e).mp h2
  refine 𝔐.pointEquivPlace.symm.injective (Subtype.ext h3)


-- created on 2026-10-23
-- updated on 2026-10-26
