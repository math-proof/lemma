module

public import Def.AlgebraicCurve_GluedPic0
public import Theorem.Scheme.AlgebraicCurveBaseChangeGalois

@[expose] public section

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

open scoped Pointwise

section Functoriality

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace SemilinearAut

variable (S : Finset (Place K F × Place K F))

def IsNodeStable (g : SemilinearAut K F) : Prop :=
  ∀ s ∈ S, (g • s.1, g • s.2) ∈ S

variable (g : SemilinearAut K F)

def nodePerm (hstab : IsNodeStable S g) : ↥S ≃ ↥S :=
  Equiv.ofBijective
    (fun s => ⟨(g • (s : Place K F × Place K F).1, g • (s : Place K F × Place K F).2),
      hstab _ s.2⟩)
    (Finite.injective_iff_bijective.mp (by
      intro s t hst
      have h1 := congrArg (fun z : ↥S => (z : Place K F × Place K F).1) hst
      have h2 := congrArg (fun z : ↥S => (z : Place K F × Place K F).2) hst
      apply Subtype.ext
      refine Prod.ext ?_ ?_
      · exact MulAction.injective g (by simpa using h1)
      · exact MulAction.injective g (by simpa using h2)))

def baseAutUnitsHom : Additive Kˣ →+ Additive Kˣ :=
  AddMonoidHom.mk'
    (fun x => Additive.ofMul (Units.map ((baseAut g : K →+* K) : K →* K) x.toMul))
    (fun x y => by simp)

def gluingMap (hstab : IsNodeStable S g) :
    GluingData K F S →+ GluingData K F S :=
  AddMonoidHom.mk'
    (fun x => (g • x.1, g • x.2.1,
      fun t => baseAutUnitsHom g (x.2.2 ((nodePerm S g hstab).symm t))))
    (fun x y => by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp [smul_add]
      · simp [smul_add]
      · funext t
        simp)

def admissibleMap (hstab : IsNodeStable S g) :
    ↥(GluingData.admissible S) →+ ↥(GluingData.admissible S) :=
  ((gluingMap S g hstab).domRestrict (GluingData.admissible S)).codRestrict _
    (fun x => gluingMap_mem_admissible S g hstab x.2)

end SemilinearAut

namespace GluedPic0

open SemilinearAut

variable (S : Finset (Place K F × Place K F)) (g : SemilinearAut K F)

def glueMap (hstab : IsNodeStable S g) : GluedPic0 K F S →+ GluedPic0 K F S :=
  QuotientAddGroup.map _ _ (admissibleMap S g hstab) (by
    rintro x hx
    simp only [AddSubgroup.mem_addSubgroupOf] at hx ⊢
    exact gluingMap_mem_gluedPrincipal S g hstab hx)

end GluedPic0

end Functoriality

end AlgebraicCurve

end

end
