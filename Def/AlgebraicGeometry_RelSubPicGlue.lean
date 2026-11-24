module
public import Mathlib
public import Def.CategoryTheory_OverTotalPresheaf
public import Theorem.CategoryTheory_OverTotalPresheaf
public import Def.AlgebraicGeometry_LocalRepresentabilityULift
public import Def.AlgebraicGeometry_RelSubPicPresheaf
public import Instance.AlgebraicGeometry_RelSubPicGlue
set_option autoImplicit false


public section

universe w v u


namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian Opposite

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicCondition c ε}

noncomputable def designationOfRepresentableBy {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) : RelativePic0Designation R c where
  P := Y
  toBase := p
  zeroSection := (e.homEquiv.symm
    (⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)), P.unit_mem _⟩ :
      (relSubPicPresheaf c ε P).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))))).left
  zeroSection_toBase := Over.w _

noncomputable abbrev relSubPicTotalSheaf
    (hG : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))) (relSubPicPresheaf c ε P)) :
    Sheaf Scheme.zariskiTopology (Type (u + 1)) :=
  ⟨(relSubPicPresheaf c ε P).overTotal,
    (isSheaf_iff_isSheaf_of_type _ _).2 ((relSubPicPresheaf c ε P).overTotal_isSheaf _ hG)⟩

section glue

variable (hG : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R))) (relSubPicPresheaf c ε P))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε P).overTotal)
  (hf : ∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i))
  [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f)]

noncomputable def gluedDesignation : RelativePic0Designation R c :=
  designationOfRepresentableBy (Functor.RepresentableBy.ofOverTotal
    (Scheme.LocalRepresentabilityULift.representableBy (F := relSubPicTotalSheaf hG) (f := f) hf))

end glue

end AlgebraicGeometry.RelPicard
