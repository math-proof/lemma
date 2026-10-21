import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma FinProdAux.isIso_sigmaSpec
  {ι : Type u} [Finite ι] (A : ι → (CommRingCat : Type (u + 1))) :
  -- imply
  IsIso (AlgebraicGeometry.sigmaSpec A) := inferInstance

/--
[AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_bijective_pi_map_of_fppf_sheaf.lean)
-/
@[path]
private lemma main
  (E : Sheaf Scheme.fppfTopology (AddCommGrpCat : Type (u + 2)))
  {ι : Type u} [Finite ι]
  (A : ι → (CommRingCat : Type (u + 1))) :
  -- imply
  Function.Bijective (fun (x : ToType (E.obj.obj (op (Spec (CommRingCat.of (∀ i, A i)))))) (i : ι) => E.obj.map (Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => A i) i))).op x) := by
  -- proof
  classical
  let F : Opposite (Scheme : Type (u + 1)) ⥤ Type (u + 1) := Functor.comp E.obj (forget (AddCommGrpCat : Type (u + 2)))
  have hF : Presieve.IsSheaf Scheme.fppfTopology F := (isSheaf_iff_isSheaf_of_type _ _).mp ((Presheaf.isSheaf_iff_isSheaf_forget Scheme.fppfTopology E.obj (forget (AddCommGrpCat : Type (u + 2)))).mp E.property)
  have hle : Scheme.zariskiTopology ≤ Scheme.fppfTopology := Precoverage.toGrothendieck_mono Scheme.zariskiPrecoverage_le_fppfPrecoverage
  have hZ : Presieve.IsSheaf Scheme.zariskiTopology F := Presieve.isSheaf_of_le F hle hF
  let _ : PreservesLimitsOfShape (Discrete ι) F := preservesLimitsOfShape_discrete_of_isSheaf_zariskiTopology hZ
  let X : ι → (Scheme : Type (u + 1)) := fun i => Spec (A i)
  let c : Cofan X := Cofan.mk (Spec (CommRingCat.of (∀ i, A i))) (fun i => Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun i => A i) i)))
  let hiso : IsIso (AlgebraicGeometry.sigmaSpec A) := FinProdAux.isIso_sigmaSpec A
  have hc : IsColimit c := (coproductIsCoproduct X).ofIsoColimit (Cocone.ext (@asIso _ _ _ _ (AlgebraicGeometry.sigmaSpec A) hiso) (by rintro ⟨i⟩; apply ι_sigmaSpec A i))
  have hl : IsLimit (F.mapCone c.op) := isLimitOfPreserves F (Cofan.IsColimit.op hc)
  let t := Types.isLimitEquivSections hl
  have hsec : ∀ (v : ∀ i, F.obj (op (X i))), (fun j : Discrete ι => (v j.as : (Functor.comp (Discrete.functor fun i => op (X i)) F).obj j)) ∈ (Functor.comp (Discrete.functor fun i => op (X i)) F).sections := by
    intro v j j' f
    obtain ⟨i⟩ := j
    obtain ⟨i'⟩ := j'
    obtain rfl : i = i' := Discrete.eq_of_hom f
    rw [show f = 𝟙 _ from Subsingleton.elim _ _, CategoryTheory.Functor.map_id]
    rfl
  change Function.Bijective (fun (x : F.obj (op c.pt)) (i : ι) => F.map (c.inj i).op x)
  have key : ∀ (x : F.obj (op c.pt)) (i : ι), F.map (c.inj i).op x = (t x).1 ⟨i⟩ := fun x i => (Types.isLimitEquivSections_apply hl ⟨i⟩ x).symm
  constructor
  ·
    intro x y hxy
    apply t.injective
    refine Subtype.ext (funext fun ⟨i⟩ => ?_)
    rw [← key, ← key]
    apply congrFun hxy i
  ·
    intro v
    refine ⟨t.symm ⟨_, hsec v⟩, funext fun i => ?_⟩
    change F.map (c.inj i).op (t.symm ⟨_, hsec v⟩) = v i
    rw [key, Equiv.apply_symm_apply]


-- created on 2026-10-20
