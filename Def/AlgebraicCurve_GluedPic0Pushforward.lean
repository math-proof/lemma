import Lemma.AlgebraicCurve.GluedPic0
import Lemma.AlgebraicCurve.Correspondence

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

section PushforwardAlong

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace GluingData

variable (S' : Finset (Place K F' × Place K F')) (S : Finset (Place K F × Place K F))
variable [DecidableEq ↥S] (ν : ↥S' → ↥S) (m : ↥S' → ℕ)

def nodeFibreSum : (↥S' → Additive Kˣ) →+ (↥S → Additive Kˣ) :=
  AddMonoidHom.mk' (fun w n => ∑ n' with ν n' = n, m n' • w n') (fun w w' => by
    funext n
    rw [Pi.add_apply, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n' _ => smul_add (m n') (w n') (w' n'))

@[simp]
theorem nodeFibreSum_apply (w : ↥S' → Additive Kˣ) (n : ↥S) :
    nodeFibreSum S' S ν m w n = ∑ n' with ν n' = n, m n' • w n' :=
  rfl

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def pushforwardMap : GluingData K F' S' →+ GluingData K F S :=
  AddMonoidHom.mk'
    (fun x => (Divisor.pushforwardAlong φ hφ x.1, Divisor.pushforwardAlong φ hφ x.2.1,
      nodeFibreSum S' S ν m x.2.2))
    (fun x y => by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · simp
      · simp
      · simp)

@[simp]
theorem pushforwardMap_apply (x : GluingData K F' S') :
    pushforwardMap S' S ν m φ hφ x
      = (Divisor.pushforwardAlong φ hφ x.1, Divisor.pushforwardAlong φ hφ x.2.1,
          nodeFibreSum S' S ν m x.2.2) :=
  rfl


end GluingData

namespace GluedPic0

variable (S' : Finset (Place K F' × Place K F')) (S : Finset (Place K F × Place K F))
variable [DecidableEq ↥S] (ν : ↥S' → ↥S) (m : ↥S' → ℕ)
variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

def admissiblePushforwardMap
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S) :
    ↥(GluingData.admissible S') →+ ↥(GluingData.admissible S) :=
  ((GluingData.pushforwardMap S' S ν m φ hφ).domRestrict (GluingData.admissible S')).codRestrict _
    (fun x => hadm x x.2)

@[simp]
theorem coe_admissiblePushforwardMap
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (x : ↥(GluingData.admissible S')) :
    (admissiblePushforwardMap S' S ν m φ hφ hadm x : GluingData K F S)
      = GluingData.pushforwardMap S' S ν m φ hφ (x : GluingData K F' S') :=
  rfl

def pushforwardMap
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (hprin : ∀ x : GluingData K F' S', GluingData.IsGluedPrincipal S' x →
      GluingData.IsGluedPrincipal S (GluingData.pushforwardMap S' S ν m φ hφ x)) :
    GluedPic0 K F' S' →+ GluedPic0 K F S :=
  QuotientAddGroup.map _ _ (admissiblePushforwardMap S' S ν m φ hφ hadm) (by
    rintro x hx
    simp only [AddSubgroup.mem_addSubgroupOf] at hx ⊢
    exact hprin _ hx)

@[simp]
theorem pushforwardMap_mk
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (hprin : ∀ x : GluingData K F' S', GluingData.IsGluedPrincipal S' x →
      GluingData.IsGluedPrincipal S (GluingData.pushforwardMap S' S ν m φ hφ x))
    (x : ↥(GluingData.admissible S')) :
    pushforwardMap S' S ν m φ hφ hadm hprin (mk S' x)
      = mk S (admissiblePushforwardMap S' S ν m φ hφ hadm x) :=
  rfl


end GluedPic0

end PushforwardAlong

end AlgebraicCurve

end
