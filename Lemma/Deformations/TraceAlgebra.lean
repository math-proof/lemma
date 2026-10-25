import Mathlib
import Lemma.Deformations.LiftFunctor
import Abbrev.Deformations_TraceAlgebra

set_option autoImplicit false

universe u

open CategoryTheory IsLocalRing

namespace Deformation

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]
variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

variable (n) in
lemma mem_conjKer_iff {R : ProartinianCat 𝓞} (γ : ConjAct (GL n R)) :
    γ ∈ conjKer (n := n) R ↔
      Matrix.GeneralLinearGroup.map (ProartinianCat.toResidueField R).hom.toRingHom
        (ConjAct.ofConjAct γ) = 1 :=
  Iff.rfl

omit [IsLocalRing 𝓞] in
@[simp]
lemma mapRepn_apply {A B : ProartinianCat 𝓞} (f : A ⟶ B) (ρ : G →ₜ* GL n A) (g : G) :
    mapRepn n G 𝓞 f ρ g = Matrix.GeneralLinearGroup.map f.hom.toRingHom (ρ g) :=
  rfl

omit [IsLocalRing 𝓞] in

lemma conjAct_smul_apply {R : ProartinianCat 𝓞} (γ : ConjAct (GL n R))
    (ρ : G →ₜ* GL n R) (g : G) :
    (γ • ρ) g = ConjAct.ofConjAct γ * ρ g * (ConjAct.ofConjAct γ)⁻¹ :=
  rfl

section TraceAlgebra

open ProartinianCat

variable (𝓞) in

def traceSet {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) : Set A.carrier :=
  Set.range fun g => Matrix.trace ((ρ g : GL n A.carrier) : Matrix n n A.carrier)

variable (𝓞) in

def traceSubalgebra {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) : Subalgebra 𝓞 A.carrier :=
  (Algebra.adjoin 𝓞 (traceSet 𝓞 ρ)).topologicalClosure

omit [IsLocalRing 𝓞] in
lemma isClosed_traceSubalgebra {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) :
    IsClosed ((traceSubalgebra 𝓞 ρ : Subalgebra 𝓞 A.carrier) : Set A.carrier) :=
  Subalgebra.isClosed_topologicalClosure _

omit [IsLocalRing 𝓞] in
lemma trace_mem_traceSubalgebra {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) (g : G) :
    Matrix.trace ((ρ g : GL n A.carrier) : Matrix n n A.carrier) ∈ traceSubalgebra 𝓞 ρ :=
  (Algebra.adjoin 𝓞 (traceSet 𝓞 ρ)).le_topologicalClosure
    (Algebra.subset_adjoin ⟨g, rfl⟩)

omit [IsLocalRing 𝓞] in

lemma traceSubalgebra_le {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) {T : Subalgebra 𝓞 A.carrier}
    (hT : IsClosed (T : Set A.carrier))
    (h : ∀ g, Matrix.trace ((ρ g : GL n A.carrier) : Matrix n n A.carrier) ∈ T) :
    traceSubalgebra 𝓞 ρ ≤ T :=
  Subalgebra.topologicalClosure_minimal
    (Algebra.adjoin_le (by rintro _ ⟨g, rfl⟩; exact h g)) hT

end TraceAlgebra

section TraceConj

omit [IsLocalRing 𝓞] in

lemma trace_smul_eq {A : ProartinianCat 𝓞} (γ : ConjAct (GL n A.carrier))
    (ρ : G →ₜ* GL n A) (g : G) :
    Matrix.trace (((γ • ρ) g : GL n A.carrier) : Matrix n n A.carrier) =
      Matrix.trace ((ρ g : GL n A.carrier) : Matrix n n A.carrier) := by
  have h1 : ((γ • ρ) g : GL n A.carrier) =
      ConjAct.ofConjAct γ * ρ g * (ConjAct.ofConjAct γ)⁻¹ := conjAct_smul_apply γ ρ g
  rw [h1]
  have h2 : ((ConjAct.ofConjAct γ * ρ g * (ConjAct.ofConjAct γ)⁻¹ : GL n A.carrier) :
      Matrix n n A.carrier) =
      ((ConjAct.ofConjAct γ : GL n A.carrier) : Matrix n n A.carrier) *
        ((ρ g : GL n A.carrier) : Matrix n n A.carrier) *
        ((↑(ConjAct.ofConjAct γ)⁻¹ : GL n A.carrier) : Matrix n n A.carrier) := by
    rw [Units.val_mul, Units.val_mul]
  rw [h2]
  exact Matrix.trace_units_conj (ConjAct.ofConjAct γ) _

omit [IsLocalRing 𝓞] in

lemma trace_mapRepn {A B : ProartinianCat 𝓞} (f : A ⟶ B) (ρ : G →ₜ* GL n A) (g : G) :
    Matrix.trace ((mapRepn n G 𝓞 f ρ g : GL n B.carrier) : Matrix n n B.carrier) =
      f.hom (Matrix.trace ((ρ g : GL n A.carrier) : Matrix n n A.carrier)) := by
  have h1 : ((mapRepn n G 𝓞 f ρ g : GL n B.carrier) : Matrix n n B.carrier) =
      ((ρ g : GL n A.carrier) : Matrix n n A.carrier).map f.hom.toRingHom := by
    rw [mapRepn_apply]
    rfl
  rw [h1]
  exact (AddMonoidHom.map_trace f.hom.toRingHom _).symm

end TraceConj

section Universal

open ProartinianCat

def TraceAlgebra.Descends {A : ProartinianCat 𝓞} (ρ : G →ₜ* GL n A) : Prop :=
  ∃ γ ∈ conjKer (n := n) A, ∀ (g : G) (i j : n),
    (((γ • ρ) g : GL n A.carrier) : Matrix n n A.carrier) i j ∈ traceSubalgebra 𝓞 ρ

end Universal

end Deformation
