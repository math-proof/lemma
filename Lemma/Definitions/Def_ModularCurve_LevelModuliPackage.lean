import Mathlib

set_option autoImplicit false

universe u

namespace ModularCurve

structure LevelModuliDatum (A : Type u) [CommRing A] where

  Pt : (T : Type u) → [CommRing T] → [Algebra A T] → Type u

  map : {T T' : Type u} → [CommRing T] → [Algebra A T] → [CommRing T'] → [Algebra A T'] →
    (T →ₐ[A] T') → Pt T → Pt T'

  map_id : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : Pt T), map (AlgHom.id A T) x = x

  map_comp : ∀ {T T' T'' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] [CommRing T'']
    [Algebra A T''] (f : T →ₐ[A] T') (g : T' →ₐ[A] T'') (x : Pt T), map (g.comp f) x = map g (map f x)

  jOf : {T : Type u} → [CommRing T] → [Algebra A T] → Pt T → T

  jOf_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : Pt T),
    jOf (map f x) = f (jOf x)

namespace LevelModuliDatum

variable {A : Type u} [CommRing A]

structure ProblemAut (D : LevelModuliDatum.{u} A) where

  act : {T : Type u} → [CommRing T] → [Algebra A T] → D.Pt T → D.Pt T

  act_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : D.Pt T),
    act (D.map f x) = D.map f (act x)

  jOf_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T), D.jOf (act x) = D.jOf x

def ProblemAut.id (D : LevelModuliDatum.{u} A) : ProblemAut D where
  act x := x
  act_map _ _ := rfl
  jOf_act _ := rfl

def ProblemAut.comp {D : LevelModuliDatum.{u} A} (σ τ : ProblemAut D) : ProblemAut D where
  act x := σ.act (τ.act x)
  act_map f x := by rw [τ.act_map, σ.act_map]
  jOf_act x := by rw [σ.jOf_act, τ.jOf_act]

def Twist (_σA : A ≃+* A) (T : Type u) : Type u := T

instance Twist.instCommRing (σA : A ≃+* A) (T : Type u) [CommRing T] : CommRing (Twist σA T) :=
  inferInstanceAs (CommRing T)

instance Twist.instAlgebra (σA : A ≃+* A) (T : Type u) [CommRing T] [Algebra A T] : Algebra A (Twist σA T) :=
  ((algebraMap A T).comp σA.toRingHom).toAlgebra

theorem Twist.algebraMap_apply (σA : A ≃+* A) (T : Type u) [CommRing T] [Algebra A T] (a : A) :
    (algebraMap A (Twist σA T) a : T) = algebraMap A T (σA a) := rfl

def AlgHom.twist (σA : A ≃+* A) {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T']
    (f : T →ₐ[A] T') : Twist σA T →ₐ[A] Twist σA T' where
  toRingHom := (f.toRingHom : T →+* T')
  commutes' a := f.commutes (σA a)

structure SemilinearProblemAut (D : LevelModuliDatum.{u} A) (σA : A ≃+* A) where

  act : {T : Type u} → [CommRing T] → [Algebra A T] → D.Pt T → D.Pt (Twist σA T)

  act_map : ∀ {T T' : Type u} [CommRing T] [Algebra A T] [CommRing T'] [Algebra A T'] (f : T →ₐ[A] T') (x : D.Pt T),
    act (D.map f x) = D.map (AlgHom.twist σA f) (act x)

  jOf_act : ∀ {T : Type u} [CommRing T] [Algebra A T] (x : D.Pt T),
    @Eq T (D.jOf (T := Twist σA T) (act x)) (D.jOf x)

end LevelModuliDatum

structure LevelModuliPackage (A : Type u) [CommRing A] (K : Type u) [Field K] [Algebra A K] (j : K)
    (D : LevelModuliDatum.{u} A) where

  B : Subalgebra A K

  j_mem : j ∈ B

  univ : D.Pt ↥B

  jOf_univ : (D.jOf univ : ↥B) = ⟨j, j_mem⟩

  represents : ∀ (T : Type u) [CommRing T] [Algebra A T] (x : D.Pt T), ∃! φ : ↥B →ₐ[A] T, D.map φ univ = x

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
