import Mathlib
import Structure.JacJ1Iface
import Def.AlgebraicGeometry_RelativePicardFunctor
import Lemma.AlgebraicGeometry.RepresentsRelSubPic
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Def.AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Lemma.AlgebraicGeometry.RelSubPicGroup
import Lemma.AlgebraicGeometry.TwoAffineOpenCover
import Instance.AlgebraicGeometry_RigKerDualNumber
import Abbrev.AlgebraicGeometry_RigKerDualNumber

set_option autoImplicit false

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra
  GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

section Thickening

variable (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A]

theorem dualNumberReduction_comp_specMap :
    dualNumberReduction R A ≫ Scheme.TwoAffineOpenCover.specMap R (DualNumber A)
      = Scheme.TwoAffineOpenCover.specMap R A := by
  change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap R (DualNumber A))) =
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  try exact (TrivSqZeroExt.fstHom R A A).comp_algebraMap

abbrev dualNumberReductionOver :
    SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R A) (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) :=
  ⟨dualNumberReduction R A, dualNumberReduction_comp_specMap R A⟩

theorem dualNumberReduction_catches_geometric_points
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (.of k) ⟶ Spec (.of (DualNumber A))) :
    ∃ s₀ : Spec (.of k) ⟶ Spec (.of A), s₀ ≫ dualNumberReduction R A = s := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective s
  have hε : φ.hom DualNumber.eps = 0 := by
    have h2 : φ.hom DualNumber.eps * φ.hom DualNumber.eps = 0 := by
      rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
    exact mul_self_eq_zero.mp h2
  let φ₀ : A →+* k := φ.hom.comp (algebraMap A (DualNumber A))
  refine ⟨Spec.map (CommRingCat.ofHom φ₀), ?_⟩
  change Spec.map _ ≫ Spec.map _ = Spec.map φ
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom]
  refine DualNumber.ringHom_ext ?_ ?_
  · ext a
    simp only [φ₀, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
  · simp only [φ₀, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, DualNumber.fst_eps, map_zero, hε]

end Thickening

section Kernel

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
variable (c : C ⟶ Spec (.of R)) (ε : SchemeHomOver (𝟙 (Spec (.of R))) c)
variable (A : Type u) [CommRing A] [Algebra R A]

def RigKerDualNumber.Carrier : Type (u + 1) :=
  { M : RigidifiedLineBundle c ε (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) //
      Nonempty ((M.pullbackAlong (dualNumberReductionOver R A)).L ≅
        (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) }

def RigKerDualNumber : Type (u + 1) := Quotient (RigKerDualNumber.setoid c ε A)

theorem RigKerDualNumber.tensor_mem (M N : RigKerDualNumber.Carrier c ε A) :
    Nonempty (((M.1.tensor N.1).pullbackAlong (dualNumberReductionOver R A)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
  ⟨(RigidifiedLineBundle.nonempty_tensor_pullbackAlong_iso (dualNumberReductionOver R A) M.1 N.1).some ≪≫
    (M.2.some ⊗ᵢ N.2.some) ≪≫ λ_ _⟩

theorem RigKerDualNumber.unit_mem :
    Nonempty (((RigidifiedLineBundle.unit (c := c) (ε := ε)
        (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).pullbackAlong (dualNumberReductionOver R A)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
  ⟨Scheme.Modules.pullbackUnitIso _⟩

def RigKerDualNumber.mul : RigKerDualNumber c ε A → RigKerDualNumber c ε A → RigKerDualNumber c ε A :=
  Quotient.map₂ (fun M N => ⟨M.1.tensor N.1, RigKerDualNumber.tensor_mem c ε A M N⟩)
    (fun _ _ hM _ _ hN => RigidifiedLineBundle.tensor_congr hM hN)

def RigKerDualNumber.one : RigKerDualNumber c ε A :=
  Quotient.mk _ ⟨RigidifiedLineBundle.unit (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)),
    RigKerDualNumber.unit_mem c ε A⟩

end Kernel

section KerPoints

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}

noncomputable def RepresentsRelSubPic.kerPointsToRigKer (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (A : Type u) [CommRing A] [Algebra R A] :
    letI L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) D.toBase //
        dualNumberReduction R A ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1 } →
      RigKerDualNumber c ε A :=
  fun x => Quotient.mk _ ⟨h.poincare.pullbackAlong x.1, by
    letI := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut c ε) h
    letI := (algEquivZeroGroupCut c ε).commGroupObj (Opposite.op (Over.mk (Scheme.TwoAffineOpenCover.specMap R A)))
    have h1 := congrArg Subtype.val
      (RepresentsRelSubPic.homEquiv_one (P := algEquivZeroGroupCut c ε) h (Over.mk (Scheme.TwoAffineOpenCover.specMap R A)))
    have one_iso : Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (Scheme.TwoAffineOpenCover.specMap R A))).L ≅
          (RigidifiedLineBundle.unit (c := c) (ε := ε) (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
      Quotient.exact h1
    have hx : GoodReductionJacobian.schemeHomOverComp (dualNumberReduction R A)
        (dualNumberReduction_comp_specMap R A) x.1 =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one (Scheme.TwoAffineOpenCover.specMap R A) :=
      Subtype.ext x.2
    rw [← hx] at one_iso
    exact ⟨h.poincare.pullbackAlongPullbackAlongIso x.1 (dualNumberReductionOver R A) ≪≫ one_iso.some⟩⟩

end KerPoints

end AlgebraicGeometry.RelPicard

end
