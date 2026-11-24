module
public import Mathlib
public import Def.AlgebraicGeometry_OModulePresheafHom
public import Def.AlgebraicGeometry_ProjTwistDatum
public import Instance.AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
public import Abbrev.AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
set_option autoImplicit false


public section

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace OModulePresheaf

variable {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
  (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
  {q : P ⟶ Spec (.of A)}

section FramesCompat

def FramesCompat (F : OModulePresheaf q) (d : ℕ) (t : ∀ j : Fin (r + 1), F.obj (ProjSpace.pullbackChart ι j)) : Prop :=
  ∀ j l : Fin (r + 1),
    F.res (ProjSpace.pullbackOverlap_le_left ι j l) (t j) =
      ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left ι j l) (ProjSpace.frameUnit ι j l) ^ d •
        F.res (ProjSpace.pullbackOverlap_le_right ι j l) (t l)

variable {ι}

end FramesCompat

section Ambient

variable (G : ℕ → OModulePresheaf q)

def FamilyFrames : Type u := ℤ → (k : ℕ) → (j : Fin (r + 1)) → (G k).obj (ProjSpace.pullbackChart ι j)

variable {ι G}

variable (ι G)

def xEnd (l : Fin (r + 1)) : FamilyFrames ι G →ₗ[A] FamilyFrames ι G where
  toFun f := fun e k j => ProjSpace.frameUnit ι j l • f (e - 1) k j
  map_add' f g := by
    refine FamilyFrames.ext fun e k j => ?_
    exact smul_add _ _ _
  map_smul' a f := by
    refine FamilyFrames.ext fun e k j => ?_
    exact sections_smul_comm (G k) _ a _ _

def IsHomogeneousElem (e : ℤ) (f : FamilyFrames ι G) : Prop :=
  (∀ e' : ℤ, e' ≠ e → f e' = 0) ∧ (e < 0 → f e = 0) ∧
    (0 ≤ e → ∀ k : ℕ, FramesCompat ι (G k) e.toNat (f e k)) ∧ Set.Finite {k : ℕ | f e k ≠ 0}

variable {ι G}

variable (ι G)

def FamilyFrames.single (e : ℤ) (k : ℕ) (t : ∀ j : Fin (r + 1), (G k).obj (ProjSpace.pullbackChart ι j)) :
    FamilyFrames ι G :=
  fun e' => if e' = e then Pi.single (M := fun k' : ℕ => ∀ j : Fin (r + 1), (G k').obj (ProjSpace.pullbackChart ι j)) k t
    else 0

variable {ι G}

end Ambient

section Family

variable [IsAffineHom ι] (G : ℕ → OModulePresheaf q) {s : ℕ}
  (θ : Fin s → ∀ k : ℕ, AffHom (G k) (G (k + 1)))

def ySucc (m : Fin s) (f : FamilyFrames ι G) (e : ℤ) :
    (k : ℕ) → (j : Fin (r + 1)) → (G k).obj (ProjSpace.pullbackChart ι j)
  | 0, _ => 0
  | k + 1, j => (θ m k).app (framesChart ι j) (f e k j)

def yEnd (m : Fin s) : FamilyFrames ι G →ₗ[A] FamilyFrames ι G where
  toFun f := fun e => ySucc ι G θ m f e
  map_add' f g := by
    refine FamilyFrames.ext fun e k j => ?_
    cases k with
    | zero => exact (add_zero (0 : (G 0).obj _)).symm
    | succ k => exact map_add _ _ _
  map_smul' a f := by
    refine FamilyFrames.ext fun e k j => ?_
    cases k with
    | zero => exact (smul_zero a).symm
    | succ k => exact LinearMap.map_smul _ _ _

def YComm : Prop :=
  ∀ (m m' : Fin s) (k : ℕ) (U : P.affineOpens) (x : (G k).obj U.1),
    (θ m (k + 1)).app U ((θ m' k).app U x) = (θ m' (k + 1)).app U ((θ m k).app U x)

variable {ι G θ}

variable (ι G θ)

open scoped IsMulCommutative in

def polyEnd (hθ : YComm G θ) : MvPolynomial (Fin s) A →ₐ[A] Module.End A (FamilyFrames ι G) :=
  haveI := Algebra.isMulCommutative_adjoin A (s := Set.range (yEnd ι G θ))
    (by rintro _ ⟨m, rfl⟩ _ ⟨m', rfl⟩; exact yEnd_mul_comm hθ m m')
  (Algebra.adjoin A (Set.range (yEnd ι G θ))).val.comp
    (MvPolynomial.aeval fun m =>
      (⟨yEnd ι G θ m, Algebra.subset_adjoin ⟨m, rfl⟩⟩ : Algebra.adjoin A (Set.range (yEnd ι G θ))))

@[reducible] def polyModule (hθ : YComm G θ) : Module (MvPolynomial (Fin s) A) (FamilyFrames ι G) :=
  Module.compHom (FamilyFrames ι G) (polyEnd ι G θ hθ).toRingHom

variable {ι G θ}

variable (ι G θ)

def familyFramesGradedModule (hθ : YComm G θ) : ProjSpaceCech.GradedModule (MvPolynomial (Fin s) A) r :=
  letI : Module (MvPolynomial (Fin s) A) (FamilyFrames ι G) := polyModule ι G θ hθ
  { M := FamilyFrames ι G
    grade := fun e =>
      { carrier := {f | IsHomogeneousElem ι G e f}
        zero_mem' := IsHomogeneousElem.zero e
        add_mem' := fun hf hg => hf.add hg
        smul_mem' := fun p _ hf => IsHomogeneousElem.polyEnd hθ hf p }
    xMul := fun l =>
      { toFun := xEnd ι G l
        map_add' := map_add _
        map_smul' := fun p f => xEnd_polyEnd ι G θ hθ l p f }
    xMul_mem_grade := fun l _ _ hf => IsHomogeneousElem.xEnd hf l
    xMul_comm := fun l l' => LinearMap.ext fun f => LinearMap.congr_fun (xEnd_comm ι G l l') f }

variable {ι G θ}

end Family

end OModulePresheaf

end AlgebraicGeometry

end
