module
public import Mathlib
public import Instance.AlgebraicGeometry_LocalRepresentabilityULift
public import Abbrev.AlgebraicGeometry_LocalRepresentabilityULift
set_option autoImplicit false


public section

universe w v u

open CategoryTheory Category Limits Opposite


namespace AlgebraicGeometry

namespace Scheme

variable (F : Sheaf Scheme.zariskiTopology.{u} (Type (max w u)))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : (i : ι) → uliftYoneda.{w}.obj (X i) ⟶ F.obj) (hf : ∀ i, MorphismProperty.presheafULift.{w} @IsOpenImmersion (f i))

namespace LocalRepresentabilityULift

variable {F f} (i j k : ι)

set_option backward.isDefEq.respectTransparency false in
open Functor.relativelyRepresentable in

@[simps]
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j :=
    have := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip
    IsOpenImmersion.mono _
  f_id i := MorphismProperty.isIso_fst'_self_ULift IsOpenImmersion.le_monomorphisms (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by apply (hf i).rep.hom_ext' <;>
    simp [MorphismProperty.fst'_self_eq_snd_ULift IsOpenImmersion.le_monomorphisms (hf i)]
  t' i j k := lift₃ _ _ _ (pullback₃.p₂ _ _ _) (pullback₃.p₃ _ _ _) (pullback₃.p₁ _ _ _)
    (by simp) (by simp)
  t_fac i j k := (hf j).rep.hom_ext' (by simp) (by simp)
  cocycle i j k := pullback₃.hom_ext (by simp) (by simp) (by simp)
  f_open i j := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip

noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

set_option backward.isDefEq.respectTransparency false in

noncomputable def uliftYonedaGluedToSheaf :
    (GrothendieckTopology.uliftYoneda.{w} zariskiTopology).obj (glueData hf).glued ⟶ F where
  hom := uliftYonedaEquiv.symm
    ((glueData hf).sheafValGluedMk (fun i ↦ uliftYonedaEquiv (f i)) (by
      intro (i : ι) (j : ι)
      dsimp only [glueData_V, glueData_J, glueData_U, glueData_f, glueData_t]
      rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
      congr 1
      rw [← op_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op]
      erw [Functor.relativelyRepresentable.symmetry_fst, ((hf i).rep.isPullback' (f j)).w]))

variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

noncomputable def uliftYonedaIsoSheaf :
    (GrothendieckTopology.uliftYoneda.{w} zariskiTopology).obj (glueData hf).glued ≅ F :=
  asIso (uliftYonedaGluedToSheaf hf)

noncomputable def representableBy : F.obj.RepresentableBy (glueData hf).glued :=
  (Functor.RepresentableBy.equivUliftYonedaIso.{w} _ _).symm
    ((sheafToPresheaf _ _).mapIso (uliftYonedaIsoSheaf hf))

include hf in
end LocalRepresentabilityULift

end Scheme

end AlgebraicGeometry
