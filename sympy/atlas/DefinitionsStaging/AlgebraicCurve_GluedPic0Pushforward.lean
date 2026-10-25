import Lemma.Definitions.Def_AlgebraicCurve_GluedPic0
import Lemma.Definitions.Def_AlgebraicCurve_Correspondence
import Def.AlgebraicCurve_GluedPic0Pushforward

noncomputable section

open IsLocalRing

namespace AlgebraicCurve

section PushforwardAlong

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace GluingData

variable (S' : Finset (Place K F' × Place K F')) (S : Finset (Place K F × Place K F))
variable [DecidableEq ↥S] (ν : ↥S' → ↥S) (m : ↥S' → ℕ)

theorem nodeFibreSum_apply (w : ↥S' → Additive Kˣ) (n : ↥S) :
    nodeFibreSum S' S ν m w n = ∑ n' with ν n' = n, m n' • w n' :=
  rfl

variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

theorem pushforwardMap_apply (x : GluingData K F' S') :
    pushforwardMap S' S ν m φ hφ x
      = (Divisor.pushforwardAlong φ hφ x.1, Divisor.pushforwardAlong φ hφ x.2.1,
          nodeFibreSum S' S ν m x.2.2) :=
  rfl

theorem _root_.AlgebraicCurve.Divisor.pushforwardAlong_apply_eq_zero (D : Divisor K F')
    (v : Place K F) (h : ∀ w : Place K F', w.restrictAlong φ hφ = v → D w = 0) :
    Divisor.pushforwardAlong φ hφ D v = 0 := by
  classical
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  show Divisor.pushforward F D v = 0
  rw [Divisor.pushforward_apply]
  refine Finset.sum_eq_zero fun w _ => ?_
  split_ifs with hwv
  · rw [h w hwv, zero_mul]
  · rfl

theorem pushforwardMap_mem_admissible
    (hcov₁ : ∀ n ∈ S, ∀ w : Place K F', w.restrictAlong φ hφ = n.1 → ∃ n' ∈ S', n'.1 = w)
    (hcov₂ : ∀ n ∈ S, ∀ w : Place K F', w.restrictAlong φ hφ = n.2 → ∃ n' ∈ S', n'.2 = w)
    {x : GluingData K F' S'} (hx : x ∈ admissible S') :
    pushforwardMap S' S ν m φ hφ x ∈ admissible S := by
  obtain ⟨h₁, h₂, hav⟩ := hx
  refine ⟨Divisor.pushforwardAlong_mem_degZero φ hφ h₁,
    Divisor.pushforwardAlong_mem_degZero φ hφ h₂, fun n hn => ⟨?_, ?_⟩⟩
  · refine Divisor.pushforwardAlong_apply_eq_zero φ hφ x.1 n.1 fun w hw => ?_
    obtain ⟨n', hn', rfl⟩ := hcov₁ n hn w hw
    exact (hav n' hn').1
  · refine Divisor.pushforwardAlong_apply_eq_zero φ hφ x.2.1 n.2 fun w hw => ?_
    obtain ⟨n', hn', rfl⟩ := hcov₂ n hn w hw
    exact (hav n' hn').2

end GluingData

namespace GluedPic0

variable (S' : Finset (Place K F' × Place K F')) (S : Finset (Place K F × Place K F))
variable [DecidableEq ↥S] (ν : ↥S' → ↥S) (m : ↥S' → ℕ)
variable (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)

theorem coe_admissiblePushforwardMap
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (x : ↥(GluingData.admissible S')) :
    (admissiblePushforwardMap S' S ν m φ hφ hadm x : GluingData K F S)
      = GluingData.pushforwardMap S' S ν m φ hφ (x : GluingData K F' S') :=
  rfl

theorem pushforwardMap_mk
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (hprin : ∀ x : GluingData K F' S', GluingData.IsGluedPrincipal S' x →
      GluingData.IsGluedPrincipal S (GluingData.pushforwardMap S' S ν m φ hφ x))
    (x : ↥(GluingData.admissible S')) :
    pushforwardMap S' S ν m φ hφ hadm hprin (mk S' x)
      = mk S (admissiblePushforwardMap S' S ν m φ hφ hadm x) :=
  rfl

theorem pushforwardMap_nodeUnit
    (hadm : ∀ x ∈ GluingData.admissible S',
      GluingData.pushforwardMap S' S ν m φ hφ x ∈ GluingData.admissible S)
    (hprin : ∀ x : GluingData K F' S', GluingData.IsGluedPrincipal S' x →
      GluingData.IsGluedPrincipal S (GluingData.pushforwardMap S' S ν m φ hφ x))
    (w : ↥S' → Additive Kˣ) :
    pushforwardMap S' S ν m φ hφ hadm hprin (nodeUnit S' w)
      = nodeUnit S (GluingData.nodeFibreSum S' S ν m w) := by
  rw [nodeUnit_apply, nodeUnit_apply, pushforwardMap_mk]
  refine congrArg (mk S) (Subtype.ext ?_)
  rw [coe_admissiblePushforwardMap]
  exact Prod.ext (map_zero _) (Prod.ext (map_zero _) rfl)

end GluedPic0

end PushforwardAlong

end AlgebraicCurve

end
