import Lemma.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

theorem comp_rev_comp_rev {n : ℕ} (t : K.OIdx n) : (t ∘ Fin.rev) ∘ Fin.rev = t :=
  funext fun j => congrArg t (Fin.rev_rev j)

theorem ointer_le_ointer_comp_rev {n : ℕ} (t : K.OIdx n) : K.ointer t ≤ K.ointer (t ∘ Fin.rev) :=
  le_iInf fun j => iInf_le _ (Fin.rev j)

theorem ointer_comp_rev_le_ointer {n : ℕ} (t : K.OIdx n) : K.ointer (t ∘ Fin.rev) ≤ K.ointer t :=
  le_iInf fun j => (iInf_le (fun i => K.U ((t ∘ Fin.rev) i)) (Fin.rev j)).trans
    (le_of_eq (congrArg (fun i => K.U (t i)) (Fin.rev_rev j)))

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

def orev (n : ℕ) : F.ocochain K n →ₗ[R] F.ocochain K n :=
  LinearMap.pi fun t => ((-1 : ℤ) ^ (n * (n + 1) / 2)) •
    ((F.res (K.ointer_le_ointer_comp_rev t)).comp (LinearMap.proj (t ∘ Fin.rev)))

theorem orev_apply (n : ℕ) (c : F.ocochain K n) (t : K.OIdx n) :
    F.orev K n c t = ((-1 : ℤ) ^ (n * (n + 1) / 2)) • F.res (K.ointer_le_ointer_comp_rev t) (c (t ∘ Fin.rev)) := by
  simp only [orev, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.proj_apply]

end OModulePresheaf

end AlgebraicGeometry

end
