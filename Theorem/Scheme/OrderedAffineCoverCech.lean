module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.Pi
public import Structure.AlgebraicGeometry_OrderedAffineCoverCech

public noncomputable section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace


namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)


public theorem face_val {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : (K.face s j).1 = s.1 ∘ Fin.succAbove j :=
  rfl


public theorem inter_le {i : ℕ} (s : K.Idx i) (j : Fin (i + 1)) : K.inter s ≤ K.U (s.1 j) := iInf_le _ j


public theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

variable (V) in


public theorem ofAffine_U [IsAffine V] (i : PUnit.{u + 1}) : (ofAffine V).U i = ⊤ := rfl

end Scheme.OrderedAffineCover

namespace Scheme.TwoAffineOpenCover

section cover

variable {R : Type u} [CommRing R] {X : Scheme.{u}}


public theorem toOrderedAffineCover_ι : 𝒱.toOrderedAffineCover.ι = ULift.{u} (Fin 2) := rfl

public theorem toOrderedAffineCover_U_zero : 𝒱.toOrderedAffineCover.U ⟨0⟩ = 𝒱.U0 := rfl

public theorem toOrderedAffineCover_U_one : 𝒱.toOrderedAffineCover.U ⟨1⟩ = 𝒱.U1 := rfl

public theorem toOrderedAffineCover_U (i : ULift.{u} (Fin 2)) : 𝒱.toOrderedAffineCover.U i = ![𝒱.U0, 𝒱.U1] i.down := rfl

end Scheme.TwoAffineOpenCover


namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)


public theorem res_refl_apply (U : V.Opens) (x : F.obj U) : F.res (le_refl U) x = x := by
  rw [F.res_refl]; rfl


public theorem res_res {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U'') (x : F.obj U'') :
    F.res h (F.res h' x) = F.res (h.trans h') x := by
  rw [F.res_comp h h']; rfl


public theorem d_apply (i : ℕ) (c : F.cochain K i) (s : K.Idx (i + 1)) :
    F.d K i c s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) • F.res (K.inter_le_inter_face s j) (c (K.face s j)) := by
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply]


public theorem cechFinite_iff : F.CechFinite K ↔ Module.Finite R (F.H0 K) ∧ ∀ i, Module.Finite R (F.HSucc K i) :=
  Iff.rfl


public theorem isCoherent_iff : F.IsCoherent ↔ ∀ U : V.affineOpens, Module.Finite Γ(V, U.1) (F.obj U.1) := Iff.rfl


public theorem isQuasicoherent_iff : F.IsQuasicoherent ↔
    ∀ (U : V.affineOpens) (f : Γ(V, U.1)),
      (∀ x : F.obj (V.basicOpen f), ∃ (n : ℕ) (y : F.obj U.1),
          F.res (V.basicOpen_le f) y = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) • x)
        ∧ (∀ y : F.obj U.1, F.res (V.basicOpen_le f) y = 0 → ∃ n : ℕ, (f ^ n : Γ(V, U.1)) • y = 0) :=
  Iff.rfl


public theorem supportedIn_iff (Y : Closeds V) :
    F.SupportedIn Y ↔ ∀ U : V.affineOpens, ((U : V.Opens) : Set V) ∩ Y = ∅ → Subsingleton (F.obj U) :=
  Iff.rfl

variable (π) in


public theorem unit_obj (U : V.Opens) : (unit π).obj U = Γ(V, U) := rfl


public theorem unit_res_apply {U U' : V.Opens} (h : U ≤ U') (x : Γ(V, U')) :
    (unit π).res h (show (unit π).obj U' from x) = (V.presheaf.map (homOfLE h).op).hom x :=
  rfl


public theorem unit_smul (U : V.Opens) (a x : Γ(V, U)) :
    a • (show (unit π).obj U from x) = (show (unit π).obj U from a * x) := rfl


public theorem unit_algebraMap_smul (U : V.Opens) (r : R) (x : Γ(V, U)) :
    r • (show (unit π).obj U from x)
      = (show (unit π).obj U from (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r * x) :=
  rfl

section TwoChart

variable (𝒱 : V.TwoAffineOpenCover)


public theorem twoChartSections_M0 : (F.twoChartSections 𝒱).M0 = F.obj 𝒱.U0 := rfl

public theorem twoChartSections_M1 : (F.twoChartSections 𝒱).M1 = F.obj 𝒱.U1 := rfl

public theorem twoChartSections_M01 : (F.twoChartSections 𝒱).M01 = F.obj (𝒱.U0 ⊓ 𝒱.U1) := rfl

public theorem twoChartSections_r0_apply (x : F.obj 𝒱.U0) :
    (F.twoChartSections 𝒱).r0 (show (F.twoChartSections 𝒱).M0 from x) = F.res inf_le_left x := rfl

public theorem twoChartSections_r1_apply (x : F.obj 𝒱.U1) :
    (F.twoChartSections 𝒱).r1 (show (F.twoChartSections 𝒱).M1 from x) = F.res inf_le_right x := rfl

end TwoChart

end OModulePresheaf

end AlgebraicGeometry

end
