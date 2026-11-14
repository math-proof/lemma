import Mathlib
import Instance.ModularCurve_LevelModuliPackage
import Structure.ModularCurve_LevelModuliPackage

set_option autoImplicit false

universe u

namespace ModularCurve


namespace LevelModuliDatum

variable {A : Type u} [CommRing A]


def ProblemAut.id (D : LevelModuliDatum.{u} A) : ProblemAut D where
  act x := x
  act_map _ _ := rfl
  jOf_act _ := rfl

def ProblemAut.comp {D : LevelModuliDatum.{u} A} (σ τ : ProblemAut D) : ProblemAut D where
  act x := σ.act (τ.act x)
  act_map f x := by rw [τ.act_map, σ.act_map]
  jOf_act x := by rw [σ.jOf_act, τ.jOf_act]


theorem Twist.algebraMap_apply (σA : A ≃+* A) (T : Type u) [CommRing T] [Algebra A T] (a : A) :
    (algebraMap A (Twist σA T) a : T) = algebraMap A T (σA a) := rfl


end LevelModuliDatum


namespace LevelModuliPackage

variable {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K] {j : K} {D : LevelModuliDatum.{u} A}
  (P : LevelModuliPackage A K j D)

noncomputable def classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : ↥P.B →ₐ[A] T :=
  (P.represents T x).choose

theorem map_classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : D.map (P.classify x) P.univ = x :=
  (P.represents T x).choose_spec.1

theorem classify_unique {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) (φ : ↥P.B →ₐ[A] T)
    (h : D.map φ P.univ = x) : φ = P.classify x :=
  (P.represents T x).unique h (P.map_classify x) ▸ rfl

noncomputable def inducedEnd (σ : LevelModuliDatum.ProblemAut D) : ↥P.B →ₐ[A] ↥P.B := P.classify (σ.act P.univ)

theorem map_inducedEnd_univ (σ : LevelModuliDatum.ProblemAut D) : D.map (P.inducedEnd σ) P.univ = σ.act P.univ :=
  P.map_classify _

theorem algHom_eq_of_map_univ_eq (φ ψ : ↥P.B →ₐ[A] ↥P.B) (h : D.map φ P.univ = D.map ψ P.univ) : φ = ψ :=
  (P.classify_unique (D.map ψ P.univ) φ h).trans (P.classify_unique (D.map ψ P.univ) ψ rfl).symm

noncomputable def inducedSemiEnd {σA : A ≃+* A} (σ : LevelModuliDatum.SemilinearProblemAut D σA) : ↥P.B →+* ↥P.B :=
  ((P.classify (T := LevelModuliDatum.Twist σA ↥P.B) (σ.act P.univ)).toRingHom :
    ↥P.B →+* LevelModuliDatum.Twist σA ↥P.B)

theorem inducedSemiEnd_algebraMap {σA : A ≃+* A} (σ : LevelModuliDatum.SemilinearProblemAut D σA) (a : A) :
    P.inducedSemiEnd σ (algebraMap A ↥P.B a) = algebraMap A ↥P.B (σA a) :=
  (P.classify (T := LevelModuliDatum.Twist σA ↥P.B) (σ.act P.univ)).commutes a

theorem map_inducedSemiEnd_univ {σA : A ≃+* A} (σ : LevelModuliDatum.SemilinearProblemAut D σA) :
    D.map (P.classify (T := LevelModuliDatum.Twist σA ↥P.B) (σ.act P.univ)) P.univ = σ.act P.univ :=
  P.map_classify _

end LevelModuliPackage

end ModularCurve
