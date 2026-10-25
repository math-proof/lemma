import Lemma.IharaIota.Main
import Mathlib.GroupTheory.PushoutI
import Instance.IharaAmalgam

namespace Ihara

open CongruenceSubgroup

open scoped MatrixGroups

def iharaEdge (N q : ℕ) : Fin 2 → (Gamma0 (N * q) →* Gamma0 N) :=
  ![ι₀ N q, ι₁ N q]

@[simp] theorem iharaEdge_zero (N q : ℕ) : iharaEdge N q 0 = ι₀ N q := rfl

@[simp] theorem iharaEdge_one (N q : ℕ) : iharaEdge N q 1 = ι₁ N q := rfl

def iharaAmalgam (N q : ℕ) : Type :=
  Monoid.PushoutI (iharaEdge N q)

def iharaVertex (N q : ℕ) (i : Fin 2) : Gamma0 N →* iharaAmalgam N q :=
  Monoid.PushoutI.of (φ := iharaEdge N q) i

def iharaBase (N q : ℕ) : Gamma0 (N * q) →* iharaAmalgam N q :=
  Monoid.PushoutI.base (iharaEdge N q)

theorem iharaVertex_zero_iota0 (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 0 (ι₀ N q γ) = iharaBase N q γ :=
  Monoid.PushoutI.of_apply_eq_base (iharaEdge N q) 0 γ

theorem iharaVertex_one_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 1 (ι₁ N q γ) = iharaBase N q γ :=
  Monoid.PushoutI.of_apply_eq_base (iharaEdge N q) 1 γ

theorem iharaVertex_edge (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 0 (ι₀ N q γ) = iharaVertex N q 1 (ι₁ N q γ) := by
  rw [iharaVertex_zero_iota0, iharaVertex_one_iota1]

section Lift

variable {N q : ℕ} {K : Type*} [Monoid K]

def pairFamily (f₀ f₁ : Gamma0 N →* K) : (i : Fin 2) → (Gamma0 N →* K) :=
  ![f₀, f₁]

@[simp] theorem pairFamily_zero (f₀ f₁ : Gamma0 N →* K) : pairFamily f₀ f₁ 0 = f₀ := rfl

@[simp] theorem pairFamily_one (f₀ f₁ : Gamma0 N →* K) : pairFamily f₀ f₁ 1 = f₁ := rfl

theorem pairFamily_compat (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q)) :
    ∀ i : Fin 2, (pairFamily f₀ f₁ i).comp (iharaEdge N q i) = f₀.comp (ι₀ N q) := by
  intro i
  fin_cases i
  · rfl
  · exact h.symm

def iharaLift (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q)) :
    iharaAmalgam N q →* K :=
  Monoid.PushoutI.lift (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h)

theorem iharaLift_vertex (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (i : Fin 2) (g : Gamma0 N) :
    iharaLift f₀ f₁ h (iharaVertex N q i g) = pairFamily f₀ f₁ i g :=
  Monoid.PushoutI.lift_of (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h) g

theorem iharaLift_vertex_zero (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (g : Gamma0 N) : iharaLift f₀ f₁ h (iharaVertex N q 0 g) = f₀ g :=
  iharaLift_vertex f₀ f₁ h 0 g

theorem iharaLift_vertex_one (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (g : Gamma0 N) : iharaLift f₀ f₁ h (iharaVertex N q 1 g) = f₁ g :=
  iharaLift_vertex f₀ f₁ h 1 g

theorem iharaLift_base (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (γ : Gamma0 (N * q)) : iharaLift f₀ f₁ h (iharaBase N q γ) = f₀ (ι₀ N q γ) :=
  Monoid.PushoutI.lift_base (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h) γ

theorem iharaAmalgam_hom_ext {f g : iharaAmalgam N q →* K}
    (h : ∀ i : Fin 2, f.comp (iharaVertex N q i) = g.comp (iharaVertex N q i)) : f = g :=
  Monoid.PushoutI.hom_ext_nonempty h

end Lift

theorem iharaVertex_range_sup (N q : ℕ) :
    (iharaVertex N q 0).range ⊔ (iharaVertex N q 1).range = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  induction x using Monoid.PushoutI.induction_on with
  | of i g =>
    fin_cases i
    · exact Subgroup.mem_sup_left ⟨g, rfl⟩
    · exact Subgroup.mem_sup_right ⟨g, rfl⟩
  | base γ => exact Subgroup.mem_sup_left ⟨ι₀ N q γ, iharaVertex_zero_iota0 N q γ⟩
  | mul x y hx hy => exact Subgroup.mul_mem _ hx hy

end Ihara
