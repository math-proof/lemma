module
public import Mathlib
public import Def.AlgebraicGeometry_ModulesSectionsTensor
public import Instance.AlgebraicGeometry_ModulesGlueOfCocycle
public import Structure.AlgebraicGeometry_ModulesGlueOfCocycle
public import Abbrev.AlgebraicGeometry_ModulesGlueOfCocycle
set_option autoImplicit false


public section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u}


open GlueOfCocycle


namespace UnitCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U)

variable (U) in

def trivial : UnitCocycle U where
  u _ _ := 1
  refl _ := rfl
  cocycle _ _ _ := by simp only [map_one, mul_one]

def mul (c' : UnitCocycle U) : UnitCocycle U where
  u i j := c.u i j * c'.u i j
  refl i := by rw [c.refl, c'.refl, mul_one]
  cocycle i j k := by
    simp only [map_mul]
    rw [mul_mul_mul_comm, c.cocycle, c'.cocycle]

noncomputable def twist (h : ∀ i, Γ(X, U i)ˣ) : UnitCocycle U where
  u i j := rO inf_le_left (h i : Γ(X, U i)) * c.u i j * rO inf_le_right (↑(h j)⁻¹ : Γ(X, U j))
  refl i := by
    rw [c.refl, mul_one, rO_irrel inf_le_left inf_le_right, ← map_mul, Units.mul_inv, map_one]
  cocycle i j k := by
    simp only [map_mul, rO_rO]
    have hc := c.cocycle i j k

    have hj : rO ((le_inf (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j).trans
          inf_le_right) (↑(h j)⁻¹ : Γ(X, U j)) *
        rO ((le_inf (inf_le_left.trans inf_le_right) inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k).trans inf_le_left)
          (h j : Γ(X, U j)) = 1 := by
      rw [rO_irrel _ ((le_inf (inf_le_left.trans inf_le_right) inf_le_right : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k).trans inf_le_left),
        ← map_mul, Units.inv_mul, map_one]
    calc _ = rO _ (h i : Γ(X, U i)) * (rO _ (c.u i j) * rO _ (c.u j k)) *
          (rO _ (↑(h j)⁻¹ : Γ(X, U j)) * rO _ (h j : Γ(X, U j))) * rO _ (↑(h k)⁻¹ : Γ(X, U k)) := by ring
      _ = _ := by rw [hj, mul_one, hc]

noncomputable def comap {X' : Scheme.{u}} (g : X' ⟶ X) : UnitCocycle (fun i => g ⁻¹ᵁ U i) where
  u i j := (g.app (U i ⊓ U j)).hom (c.u i j)
  refl i := by rw [c.refl, map_one]; rfl
  cocycle i j k := by
    have nat : ∀ {A B : X.Opens} (hBA : B ≤ A) (s : Γ(X, A)),
        GlueOfCocycle.rO (X := X') (show g ⁻¹ᵁ B ≤ g ⁻¹ᵁ A from fun _ hx => hBA hx) ((g.app A).hom s) =
          (g.app B).hom (rO hBA s) := by
      intro A B hBA s
      have h := CategoryTheory.ConcreteCategory.congr_hom (g.naturality (homOfLE hBA).op) s
      rw [CategoryTheory.ConcreteCategory.comp_apply, CategoryTheory.ConcreteCategory.comp_apply] at h
      exact h.symm
    have := congrArg (g.app (U i ⊓ U j ⊓ U k)).hom (c.cocycle i j k)
    rw [map_mul, ← nat, ← nat, ← nat] at this
    exact this

end UnitCocycle

namespace GlueOfCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U) (T : X.Opens)

def families : AddSubgroup (∀ i, Γ(X, T ⊓ U i)) where
  carrier := {x | ∀ i j, rO (leTi T i j) (x i) = rO (leij T i j) (c.u i j) * rO (leTj T i j) (x j)}
  zero_mem' := by intro i j; simp
  add_mem' := by
    intro x y hx hy i j
    simp only [Pi.add_apply, map_add]
    rw [hx, hy, mul_add]
  neg_mem' := by
    intro x hx i j
    simp only [Pi.neg_apply, map_neg]
    rw [hx, mul_neg]

variable {c T}

variable (c T)

variable {T}

noncomputable def resFam {T T' : X.Opens} (h : T' ≤ T) : families c T →+ families c T' where
  toFun x := ⟨fun i => rO (inf_le_inf_right (U i) h) (x.1 i), by
    have hx := x.2
    rw [mem_families] at hx ⊢
    intro i j
    rw [rO_rO, rO_rO]
    have e1 : rO ((leTi T' i j).trans (inf_le_inf_right (U i) h)) (x.1 i) =
        rO (inf_le_inf_right (U i ⊓ U j) h) (rO (leTi T i j) (x.1 i)) := by rw [rO_rO]
    have e2 : rO ((leTj T' i j).trans (inf_le_inf_right (U j) h)) (x.1 j) =
        rO (inf_le_inf_right (U i ⊓ U j) h) (rO (leTj T i j) (x.1 j)) := by rw [rO_rO]
    rw [e1, e2, hx i j, map_mul, rO_rO]⟩
  map_zero' := by apply Subtype.ext; funext i; simp
  map_add' x y := by apply Subtype.ext; funext i; simp

noncomputable def preGlue : (Opens X)ᵒᵖ ⥤ Ab where
  obj T := AddCommGrpCat.of (families c T.unop)
  map {T T'} f := AddCommGrpCat.ofHom (resFam c f.unop.le)
  map_id T := by
    ext
    exact rO_refl _
  map_comp {T₁ T₂ T₃} f g := by
    ext
    exact (rO_rO _ _ _).symm

noncomputable def preGlueMod : _root_.PresheafOfModules X.ringCatSheaf.obj :=
  _root_.PresheafOfModules.ofPresheaf (preGlue c) (preGlue_map_smul c)

end GlueOfCocycle

variable {U : ι → X.Opens}

noncomputable def glueOfCocycle (c : UnitCocycle U) : X.Modules :=
  ⟨GlueOfCocycle.preGlueMod c, GlueOfCocycle.preGlue_isSheaf c⟩

noncomputable def glueComponent (c : UnitCocycle U) (T : X.Opens) (i : ι) : Γ(glueOfCocycle c, T) →+ Γ(X, T ⊓ U i) where
  toFun p := (p : GlueOfCocycle.families c T).1 i
  map_zero' := rfl
  map_add' _ _ := rfl

noncomputable def glueMk (c : UnitCocycle U) (T : X.Opens) (x : ∀ i, Γ(X, T ⊓ U i))
    (hx : ∀ i j, rO (GlueOfCocycle.leTi T i j) (x i) =
      rO (GlueOfCocycle.leij T i j) (c.u i j) * rO (GlueOfCocycle.leTj T i j) (x j)) : Γ(glueOfCocycle c, T) :=
  (⟨x, hx⟩ : GlueOfCocycle.families c T)

noncomputable def glueFrame (c : UnitCocycle U) (i : ι) : Γ(glueOfCocycle c, U i) :=
  glueMk c (U i) (fun k => rO (le_of_eq (inf_comm (U i) (U k))) (c.u k i)) fun k l => by
    rw [rO_rO, rO_rO]
    exact (c.cocycle_le k l i (GlueOfCocycle.leij (U i) k l) _ _).symm

end AlgebraicGeometry.Scheme.Modules
