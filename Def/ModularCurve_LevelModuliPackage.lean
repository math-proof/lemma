module

public import Mathlib
public import Instance.ModularCurve_LevelModuliPackage
public import Structure.ModularCurve_LevelModuliPackage

@[expose] public section

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


end LevelModuliDatum


namespace LevelModuliPackage

variable {A : Type u} [CommRing A] {K : Type u} [Field K] [Algebra A K] {j : K} {D : LevelModuliDatum.{u} A}
  (P : LevelModuliPackage A K j D)

noncomputable def classify {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T) : ↥P.B →ₐ[A] T :=
  (P.represents T x).choose

noncomputable def inducedEnd (σ : LevelModuliDatum.ProblemAut D) : ↥P.B →ₐ[A] ↥P.B := P.classify (σ.act P.univ)

noncomputable def inducedSemiEnd {σA : A ≃+* A} (σ : LevelModuliDatum.SemilinearProblemAut D σA) : ↥P.B →+* ↥P.B :=
  ((P.classify (T := LevelModuliDatum.Twist σA ↥P.B) (σ.act P.univ)).toRingHom :
    ↥P.B →+* LevelModuliDatum.Twist σA ↥P.B)

end LevelModuliPackage

end ModularCurve

end
