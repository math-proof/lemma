import Lemma.Definitions.Def_QuaternionAlgebra_ClassSetHecke
import Lemma.Definitions.Def_CerednikDrinfeld_Ribbon

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra

noncomputable section

namespace CerednikDrinfeld

variable {a b : ℚ}

def meetOrder (R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : Submodule ℤ ℍ[ℚ, a, b] :=
  R ⊓ Submodule.conjByFiniteIdele R n

def classSetForget (U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x : ClassSet U) :
    ClassSet U' :=
  ClassSet.mk U' x.out

def classSetShift (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (x : ClassSet U) : ClassSet U :=
  ClassSet.mk U (x.out * n)

def unitWeight (Λ : Submodule ℤ ℍ[ℚ, a, b]) : ℕ+ :=
  Nat.toPNat' (Nat.card {u : ℍ[ℚ, a, b] // IsUnitOf Λ u} / 2)

def classWeight (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (Λ : Submodule ℤ ℍ[ℚ, a, b])
    (x : ClassSet U) : ℕ+ :=
  unitWeight (Submodule.conjByFiniteIdele Λ x.out)

def classSetHeckeMatrix (U : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (T : Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    Matrix (ClassSet U) (ClassSet U) ℤ :=
  Matrix.of fun i j => heckeKernel U T j i

def uHeckeSet (R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) (q : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {h | h ∈ primeHeckeSet (meetOrder R n) q ∧
    Submodule.conjByFiniteIdele (Submodule.conjByFiniteIdele R n) h = R ∧
    Submodule.conjByFiniteIdele R h ≠ Submodule.conjByFiniteIdele R n}

def levelHeckeUSet (Λ O : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : ℕ) :
    Set (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ :=
  {h | h ∈ primeHeckeSet O ℓ ∧ Submodule.conjByFiniteIdele O h ≠ O ∧ ¬ O ≤ Submodule.conjByFiniteIdele Λ h}

def classSetDegeneracyData (R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    DegeneracyData (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))
      (ClassSet (Submodule.finiteIdeleStabilizer R)) where
  a := classSetForget _ _
  b x := ClassSet.mk _ (x.out * n)
  w := classWeight _ (meetOrder R n)

def classSetEdgeHecke (N q : ℕ) (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
    (ℓ : Nat.Primes) :
    Matrix (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))
      (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n))) ℤ :=
  if (ℓ : ℕ) = q then classSetHeckeMatrix _ (uHeckeSet R n q)
  else if (ℓ : ℕ) ∣ N then classSetHeckeMatrix _ (levelHeckeUSet Λ (meetOrder R n) ℓ)
  else classSetHeckeMatrix _ (primeHeckeSet (meetOrder R n) ℓ)

def classSetVertexHecke (N : ℕ) (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (ℓ : Nat.Primes) :
    Matrix (ClassSet (Submodule.finiteIdeleStabilizer R)) (ClassSet (Submodule.finiteIdeleStabilizer R)) ℤ :=
  if (ℓ : ℕ) ∣ N then classSetHeckeMatrix _ (levelHeckeUSet Λ R ℓ)
  else classSetHeckeMatrix _ (primeHeckeSet R ℓ)

section Laws

variable (N q : ℕ) [Fact q.Prime] (Λ R : Submodule ℤ ℍ[ℚ, a, b]) (n : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)
  [Fintype (ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)))]
  [Fintype (ClassSet (Submodule.finiteIdeleStabilizer R))]
  [DecidableEq (ClassSet (Submodule.finiteIdeleStabilizer R))]

def ClassSetHeckeLaws : Prop :=
  (∀ ℓ ℓ' : Nat.Primes, Commute (classSetEdgeHecke N q Λ R n ℓ) (classSetEdgeHecke N q Λ R n ℓ')) ∧
  (∀ ℓ ℓ' : Nat.Primes, Commute (classSetVertexHecke N Λ R ℓ) (classSetVertexHecke N Λ R ℓ')) ∧
  (∀ ℓ : Nat.Primes, ℓ ∉ ({⟨q, Fact.out⟩} : Finset Nat.Primes) → ∀ i : Fin 2,
    ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ,
      jointDelta (classSetDegeneracyData R n) i ((classSetEdgeHecke N q Λ R n ℓ).mulVecLin x) =
        (classSetVertexHecke N Λ R ℓ).mulVecLin (jointDelta (classSetDegeneracyData R n) i x)) ∧
  (∀ ℓ : Nat.Primes, ∀ x : ClassSet (Submodule.finiteIdeleStabilizer (meetOrder R n)) → ℤ,
    (∀ i, jointDelta (classSetDegeneracyData R n) i x = 0) →
      ∀ i, jointDelta (classSetDegeneracyData R n) i ((classSetEdgeHecke N q Λ R n ℓ).mulVecLin x) = 0)

open Classical in

def classSetHeckeData : HeckeData (classSetDegeneracyData R n) :=
  if h : ClassSetHeckeLaws N q Λ R n then
    { T := classSetEdgeHecke N q Λ R n
      Tv := classSetVertexHecke N Λ R
      comm := h.1
      commv := h.2.1
      S := {⟨q, Fact.out⟩}
      good_equivariant := h.2.2.1
      kernel_stable := h.2.2.2 }
  else
    { T := 0
      Tv := 0
      comm := fun _ _ => Commute.refl 0
      commv := fun _ _ => Commute.refl 0
      S := {⟨q, Fact.out⟩}
      good_equivariant := fun _ _ i x => by
        simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero]
      kernel_stable := fun _ x _ i => by
        simp only [Pi.zero_apply, LinearMap.zero_apply, map_zero] }

end Laws

end CerednikDrinfeld

end
