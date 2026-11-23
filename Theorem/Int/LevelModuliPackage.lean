module

public import Mathlib
public import Instance.ModularCurve_LevelModuliPackage
public import Structure.ModularCurve_LevelModuliPackage

public section

set_option autoImplicit false

universe u

namespace ModularCurve


namespace LevelModuliDatum

variable {A : Type u} [CommRing A]


public theorem Twist.algebraMap_apply (σA : A ≃+* A) (T : Type u) [CommRing T] [Algebra A T] (a : A) :
    (algebraMap A (Twist σA T) a : T) = algebraMap A T (σA a) := rfl


end LevelModuliDatum


namespace LevelModuliPackage

variable {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K] {j : K} {D : LevelModuliDatum.{u} A}
  (P : LevelModuliPackage A K j D)


public theorem map_classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : D.map (P.classify x) P.univ = x :=
  (P.represents T x).choose_spec.1


public theorem classify_unique {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) (φ : ↥P.B →ₐ[A] T)
    (h : D.map φ P.univ = x) : φ = P.classify x :=
  (P.represents T x).unique h (P.map_classify x) ▸ rfl


public theorem map_inducedEnd_univ (σ : LevelModuliDatum.ProblemAut D) : D.map (P.inducedEnd σ) P.univ = σ.act P.univ :=
  P.map_classify _


public theorem algHom_eq_of_map_univ_eq (φ ψ : ↥P.B →ₐ[A] ↥P.B) (h : D.map φ P.univ = D.map ψ P.univ) : φ = ψ :=
  (P.classify_unique (D.map ψ P.univ) φ h).trans (P.classify_unique (D.map ψ P.univ) ψ rfl).symm


public theorem inducedSemiEnd_algebraMap {σA : A ≃+* A} (σ : LevelModuliDatum.SemilinearProblemAut D σA) (a : A) :
    P.inducedSemiEnd σ (algebraMap A ↥P.B a) = algebraMap A ↥P.B (σA a) :=
  (P.classify (T := LevelModuliDatum.Twist σA ↥P.B) (σ.act P.univ)).commutes a


public theorem map_inducedSemiEnd_univ {σA : A ≃+* A} (σ : LevelModuliDatum.SemilinearProblemAut D σA) :
    D.map (P.classify (T := LevelModuliDatum.Twist σA ↥P.B) (σ.act P.univ)) P.univ = σ.act P.univ :=
  P.map_classify _

end LevelModuliPackage

end ModularCurve
