module

public import Theorem.Matrix.IharaIota
public import Mathlib.GroupTheory.PushoutI
public import Instance.IharaAmalgam

public section

namespace Ihara

open CongruenceSubgroup

open scoped MatrixGroups


@[simp] public theorem iharaEdge_zero (N q : ℕ) : iharaEdge N q 0 = ι₀ N q := rfl


@[simp] public theorem iharaEdge_one (N q : ℕ) : iharaEdge N q 1 = ι₁ N q := rfl


public theorem iharaVertex_zero_iota0 (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 0 (ι₀ N q γ) = iharaBase N q γ :=
  Monoid.PushoutI.of_apply_eq_base (iharaEdge N q) 0 γ


public theorem iharaVertex_one_iota1 (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 1 (ι₁ N q γ) = iharaBase N q γ :=
  Monoid.PushoutI.of_apply_eq_base (iharaEdge N q) 1 γ


public theorem iharaVertex_edge (N q : ℕ) (γ : Gamma0 (N * q)) :
    iharaVertex N q 0 (ι₀ N q γ) = iharaVertex N q 1 (ι₁ N q γ) := by
  rw [iharaVertex_zero_iota0, iharaVertex_one_iota1]

section Lift

variable {N q : ℕ} {K : Type*} [Monoid K]


@[simp] public theorem pairFamily_zero (f₀ f₁ : Gamma0 N →* K) : pairFamily f₀ f₁ 0 = f₀ := rfl


@[simp] public theorem pairFamily_one (f₀ f₁ : Gamma0 N →* K) : pairFamily f₀ f₁ 1 = f₁ := rfl


public theorem pairFamily_compat (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q)) :
    ∀ i : Fin 2, (pairFamily f₀ f₁ i).comp (iharaEdge N q i) = f₀.comp (ι₀ N q) := by
  intro i
  fin_cases i
  · rfl
  · exact h.symm


public theorem iharaLift_vertex (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (i : Fin 2) (g : Gamma0 N) :
    iharaLift f₀ f₁ h (iharaVertex N q i g) = pairFamily f₀ f₁ i g :=
  Monoid.PushoutI.lift_of (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h) g


public theorem iharaLift_vertex_zero (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (g : Gamma0 N) : iharaLift f₀ f₁ h (iharaVertex N q 0 g) = f₀ g :=
  iharaLift_vertex f₀ f₁ h 0 g


public theorem iharaLift_vertex_one (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (g : Gamma0 N) : iharaLift f₀ f₁ h (iharaVertex N q 1 g) = f₁ g :=
  iharaLift_vertex f₀ f₁ h 1 g


public theorem iharaLift_base (f₀ f₁ : Gamma0 N →* K) (h : f₀.comp (ι₀ N q) = f₁.comp (ι₁ N q))
    (γ : Gamma0 (N * q)) : iharaLift f₀ f₁ h (iharaBase N q γ) = f₀ (ι₀ N q γ) :=
  Monoid.PushoutI.lift_base (pairFamily f₀ f₁) (f₀.comp (ι₀ N q)) (pairFamily_compat f₀ f₁ h) γ


public theorem iharaAmalgam_hom_ext {f g : iharaAmalgam N q →* K}
    (h : ∀ i : Fin 2, f.comp (iharaVertex N q i) = g.comp (iharaVertex N q i)) : f = g :=
  Monoid.PushoutI.hom_ext_nonempty h

end Lift


public theorem iharaVertex_range_sup (N q : ℕ) :
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
