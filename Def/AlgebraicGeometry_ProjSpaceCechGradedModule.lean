import Mathlib
import Def.AlgebraicGeometry_ProjSpaceCechTwist
import Instance.AlgebraicGeometry_ProjSpaceCechGradedModule
import Structure.AlgebraicGeometry_ProjSpaceCechGradedModule
import Abbrev.AlgebraicGeometry_ProjSpaceCechGradedModule

set_option autoImplicit false

noncomputable section

universe u

open Finset Function MvPolynomial

namespace ProjSpaceCech

section Carrier

variable (R : Type u) [CommRing R] (n : ℕ)


variable {R n}
variable (D : GradedModule R n)

def GradedModule.monMul (a : Fin (n + 1) → ℕ) : D.M →ₗ[R] D.M :=
  Finset.univ.noncommProd (fun j => D.xMul j ^ a j)
    (fun j _ k _ _ => GradedModule.xMul_pow_commute D j k (a j) (a k))

end Carrier

section GradSec

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n) (I : Finset (Fin (n + 1)))


def GradedModule.Frac.Rel (x y : GradedModule.Frac D I) : Prop :=
  ∃ (c : Fin (n + 1) → ℕ) (_ : ∀ j ∉ I, c j = 0),
    GradedModule.monMul D (c + y.denExp) x.num = GradedModule.monMul D (c + x.denExp) y.num

def GradedModule.sec : Type u := Quotient (GradedModule.Frac.setoid D I)

def GradedModule.sec.mk (x : GradedModule.Frac D I) : GradedModule.sec D I := ⟦x⟧

def GradedModule.secMkAt (a : Fin (n + 1) → ℕ) (ha : ∀ j ∉ I, a j = 0) :
    D.grade (∑ j, (a j : ℤ)) →ₗ[R] GradedModule.sec D I where
  toFun m := GradedModule.sec.mk D I ⟨a, ha, m.1, m.2⟩
  map_add' m m' := GradedModule.sec_mk_add D I a ha m.2 m'.2
  map_smul' r m := by
    simp only [RingHom.id_apply, GradedModule.sec_mk_smul]; rfl

def GradedModule.secIncl {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) :
    GradedModule.sec D I →ₗ[R] GradedModule.sec D J where
  toFun := Quotient.map
    (fun x => ⟨x.denExp, fun j hj => x.hden j (fun h => hj (hIJ h)), x.num, x.hnum⟩)
    (fun _ _ ⟨c, hc, heq⟩ => ⟨c, fun j hj => hc j (fun h => hj (hIJ h)), heq⟩)
  map_add' := by
    rintro ⟨x⟩ ⟨y⟩
    exact (GradedModule.sec_mk_eq D J).mpr ⟨0, fun _ _ => rfl, by simp⟩
  map_smul' := by
    rintro r ⟨x⟩
    exact (GradedModule.sec_mk_eq D J).mpr ⟨0, fun _ _ => rfl, by simp⟩

end GradSec

section GradAltC

variable {R : Type u} [CommRing R] {n : ℕ}
variable (D : GradedModule R n)

abbrev GradedModule.cochain (i : ℕ) : Type u :=
  ∀ s : Idx n i, GradedModule.sec D (Idx.img n s)

def GradedModule.faceRes {i : ℕ} (s : Idx n (i + 1)) (j : Fin (i + 2)) :
    GradedModule.sec D (Idx.img n (Idx.face n s j))
      →ₗ[R] GradedModule.sec D (Idx.img n s) :=
  GradedModule.secIncl D (Idx.img_face_subset n s j)

def GradedModule.d (i : ℕ) :
    GradedModule.cochain D i →ₗ[R] GradedModule.cochain D (i + 1) :=
  LinearMap.pi fun s => ∑ j : Fin (i + 2), (-1 : R) ^ (j : ℕ) •
    (GradedModule.faceRes D s j).comp (LinearMap.proj (Idx.face n s j))

def GradedModule.H : ℕ → Type u
  | 0 => LinearMap.ker (GradedModule.d D 0)
  | (i + 1) =>
      LinearMap.ker (GradedModule.d D (i + 1)) ⧸
        (LinearMap.range (GradedModule.d D i)).comap
          (LinearMap.ker (GradedModule.d D (i + 1))).subtype

end GradAltC


section Instances

variable (R : Type u) [CommRing R] (n : ℕ)


variable {R n}


def GradedModule.quot (D : GradedModule R n) (K : Submodule R D.M)
    (hstab : ∀ j, ∀ m ∈ K, D.xMul j m ∈ K) : GradedModule R n where
  M := D.M ⧸ K
  grade d := (D.grade d).map K.mkQ
  xMul j := K.mapQ K (D.xMul j) (fun m hm => hstab j m hm)
  xMul_mem_grade j d := by
    rintro _ ⟨m, hm, rfl⟩; exact ⟨D.xMul j m, D.xMul_mem_grade j d m hm, rfl⟩
  xMul_comm j k := by
    refine LinearMap.ext fun z => ?_
    obtain ⟨m, rfl⟩ := K.mkQ_surjective z
    exact congrArg K.mkQ (LinearMap.congr_fun (D.xMul_comm j k) m)

end Instances


section SubMod

variable {R : Type u} [CommRing R] {n : ℕ}

def GradedModule.sub (D : GradedModule R n) (K : Submodule R D.M)
    (hstab : ∀ j, ∀ m ∈ K, D.xMul j m ∈ K) : GradedModule R n where
  M := D.M
  grade d := D.grade d ⊓ K
  xMul := D.xMul
  xMul_mem_grade j d m hm :=
    ⟨D.xMul_mem_grade j d m hm.1, hstab j m hm.2⟩
  xMul_comm := D.xMul_comm

end SubMod

section Hom

variable {R : Type u} [CommRing R] {n : ℕ}


variable {D₁ D₂ : GradedModule R n}

def GradedModule.Hom.secMap (φ : GradedModule.Hom D₁ D₂) (I : Finset (Fin (n + 1))) :
    GradedModule.sec D₁ I →ₗ[R] GradedModule.sec D₂ I where
  toFun := Quotient.map
    (fun x => ⟨x.denExp, x.hden, φ.toLinearMap x.num, φ.mem_grade _ _ x.hnum⟩)
    (fun _ _ ⟨c, hc, heq⟩ => ⟨c, hc, by
      rw [← GradedModule.Hom.map_monMul, ← GradedModule.Hom.map_monMul, heq]⟩)
  map_add' := by
    rintro ⟨x⟩ ⟨y⟩
    refine (GradedModule.sec_mk_eq _ I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    simp only [zero_add, map_add, GradedModule.Hom.map_monMul]
  map_smul' := by
    rintro r ⟨x⟩
    refine (GradedModule.sec_mk_eq _ I).mpr ⟨0, fun _ _ => rfl, ?_⟩
    simp only [zero_add, map_smul, RingHom.id_apply]

def GradedModule.Hom.cochainMap (φ : GradedModule.Hom D₁ D₂) (i : ℕ) :
    GradedModule.cochain D₁ i →ₗ[R] GradedModule.cochain D₂ i :=
  LinearMap.pi fun s => (GradedModule.Hom.secMap φ (Idx.img n s)).comp
    (LinearMap.proj s)

def GradedModule.Hom.cochainMapKer (φ : GradedModule.Hom D₁ D₂) (i : ℕ) :
    ↥(LinearMap.ker (GradedModule.d D₁ i))
      →ₗ[R] ↥(LinearMap.ker (GradedModule.d D₂ i)) :=
  (GradedModule.Hom.cochainMap φ i).restrict fun f hf =>
    LinearMap.mem_ker.mpr <| by
      rw [← LinearMap.comp_apply, GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply,
        LinearMap.mem_ker.mp hf, map_zero]

def GradedModule.Hom.HMap (φ : GradedModule.Hom D₁ D₂) :
    (i : ℕ) → GradedModule.H D₁ i →ₗ[R] GradedModule.H D₂ i
  | 0 => GradedModule.Hom.cochainMapKer φ 0
  | (j + 1) => Submodule.mapQ _ _ (GradedModule.Hom.cochainMapKer φ (j + 1)) fun x hx => by
      obtain ⟨g, hg⟩ := hx
      exact ⟨GradedModule.Hom.cochainMap φ j g, by
        rw [← LinearMap.comp_apply, GradedModule.Hom.cochainMap_comm, LinearMap.comp_apply, hg];
        rfl⟩

end Hom

section IsFG

variable {R : Type u} [CommRing R] {n : ℕ}


abbrev GradedModule.Presentation.F {D : GradedModule R n} (σ : GradedModule.Presentation D) :
    GradedModule R n :=
  GradedModule.pi (fun k => GradedModule.FD R n (σ.d₀ k))

abbrev GradedModule.Presentation.K {D : GradedModule R n} (σ : GradedModule.Presentation D) :
    Submodule R σ.F.M := LinearMap.ker σ.hom.toLinearMap

abbrev GradedModule.Presentation.ker {D : GradedModule R n} (σ : GradedModule.Presentation D) :
    GradedModule R n :=
  GradedModule.sub σ.F σ.K (GradedModule.Presentation.K_xMul_stable σ)

def GradedModule.Presentation.kerIncl {D : GradedModule R n} (σ : GradedModule.Presentation D) :
    GradedModule.Hom σ.ker σ.F where
  toLinearMap := LinearMap.id
  mem_grade _ _ hm := hm.1
  xMul_comm _ := rfl

end IsFG


end ProjSpaceCech

end
