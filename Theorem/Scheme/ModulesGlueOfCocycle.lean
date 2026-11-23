module

public import Mathlib
public import Theorem.Scheme.ModulesSectionsTensor
public import Instance.AlgebraicGeometry_ModulesGlueOfCocycle
public import Structure.AlgebraicGeometry_ModulesGlueOfCocycle
public import Abbrev.AlgebraicGeometry_ModulesGlueOfCocycle

public section

set_option autoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Scheme

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {ι : Type u}

namespace GlueOfCocycle

public theorem rO_rO {A B C : X.Opens} (hBA : B ≤ A) (hCB : C ≤ B) (g : Γ(X, A)) :
    rO hCB (rO hBA g) = rO (hCB.trans hBA) g := by
  change (X.presheaf.map (homOfLE hBA).op ≫ X.presheaf.map (homOfLE hCB).op).hom g = _
  rw [← Functor.map_comp]; rfl


public theorem rO_irrel {A B : X.Opens} (h h' : B ≤ A) (g : Γ(X, A)) : rO h g = rO h' g := rfl


public theorem rO_refl {A : X.Opens} (g : Γ(X, A)) : rO (le_refl A) g = g := by
  change (X.presheaf.map (homOfLE (le_refl A)).op).hom g = g
  rw [Subsingleton.elim (homOfLE (le_refl A)) (𝟙 A), op_id, X.presheaf.map_id]; rfl


public theorem rO_rO_self {A B : X.Opens} (h : B ≤ A) (h' : A ≤ B) (g : Γ(X, B)) : rO h (rO h' g) = g := by
  rw [rO_rO]; exact rO_refl g


public theorem rO_bijective_of_le_le {A B : X.Opens} (h : B ≤ A) (h' : A ≤ B) : Function.Bijective (rO h) :=
  Function.bijective_iff_has_inverse.2 ⟨rO h', fun g => rO_rO_self h' h g, fun g => rO_rO_self h h' g⟩

end GlueOfCocycle

open GlueOfCocycle


namespace UnitCocycle

variable {U : ι → X.Opens} (c : UnitCocycle U)


public theorem cocycle_le (i j k : ι) {W : X.Opens} (hij : W ≤ U i ⊓ U j) (hjk : W ≤ U j ⊓ U k) (hik : W ≤ U i ⊓ U k) :
    rO hij (c.u i j) * rO hjk (c.u j k) = rO hik (c.u i k) := by
  have hW : W ≤ U i ⊓ U j ⊓ U k := le_inf hij (hjk.trans inf_le_right)
  have := congrArg (rO hW) (c.cocycle i j k)
  rw [map_mul, rO_rO, rO_rO, rO_rO] at this
  exact this


public theorem mul_symm (i j : ι) :
    c.u i j * rO (le_of_eq (inf_comm (U i) (U j)) : U i ⊓ U j ≤ U j ⊓ U i) (c.u j i) = 1 := by
  have h := c.cocycle_le i j i (W := U i ⊓ U j) le_rfl (le_of_eq (inf_comm _ _)) (le_inf inf_le_left inf_le_left)
  rw [rO_refl, c.refl, map_one] at h
  exact h


public theorem isUnit (i j : ι) : IsUnit (c.u i j) :=
  isUnit_iff_exists_inv.mpr ⟨_, c.mul_symm i j⟩

variable (U) in


public theorem leTi (i j : ι) : T ⊓ (U i ⊓ U j) ≤ T ⊓ U i := inf_le_inf_left T inf_le_left

public theorem leTj (i j : ι) : T ⊓ (U i ⊓ U j) ≤ T ⊓ U j := inf_le_inf_left T inf_le_right

public theorem leij (i j : ι) : T ⊓ (U i ⊓ U j) ≤ U i ⊓ U j := inf_le_right


public theorem mem_families {x : ∀ i, Γ(X, T ⊓ U i)} :
    x ∈ families c T ↔ ∀ i j, rO (leTi T i j) (x i) = rO (leij T i j) (c.u i j) * rO (leTj T i j) (x j) := Iff.rfl

variable (c T)


public theorem smul_val (g : Γ(X, T)) (x : families c T) (i : ι) : (g • x).1 i = rO inf_le_left g * x.1 i := rfl

variable {T}


public theorem resFam_val {T T' : X.Opens} (h : T' ≤ T) (x : families c T) (i : ι) :
    (resFam c h x).1 i = rO (inf_le_inf_right (U i) h) (x.1 i) := rfl


public theorem preGlue_map_smul ⦃T T' : (Opens X)ᵒᵖ⦄ (f : T ⟶ T') (r : X.ringCatSheaf.obj.obj T) (m : (preGlue c).obj T) :
    (preGlue c).map f (r • m) = X.ringCatSheaf.obj.map f r • (preGlue c).map f m := by
  apply Subtype.ext; funext i
  change rO _ (rO _ r * m.1 i) = rO _ (rO _ r) * rO _ (m.1 i)
  simp only [map_mul, rO_rO]


public theorem preGlue_isSheaf : TopCat.Presheaf.IsSheaf (preGlue c) := by
  rw [TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing]
  intro κ W sf hsf
  let T : X.Opens := iSup W
  have hWT : ∀ a, W a ≤ T := fun a => le_iSup W a

  let xs : ∀ (i : ι) (a : κ), Γ(X, W a ⊓ U i) := fun i a => (sf a).1 i
  have hx : ∀ i, TopCat.Presheaf.IsCompatible X.sheaf.obj (fun a => W a ⊓ U i) (xs i) := by
    intro i a b
    have h := congrArg (fun p : families c (W a ⊓ W b) => p.1 i) (hsf a b)
    change rO (inf_le_left : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ W a ⊓ U i) (xs i a) =
      rO (inf_le_right : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ W b ⊓ U i) (xs i b)
    have hle : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ (W a ⊓ W b) ⊓ U i :=
      le_inf (inf_le_inf inf_le_left inf_le_left) (inf_le_left.trans inf_le_right)
    have e1 : rO (inf_le_left : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ W a ⊓ U i) (xs i a) =
        rO hle (rO (inf_le_inf_right (U i) inf_le_left) (xs i a)) := by rw [rO_rO]
    have e2 : rO (inf_le_right : (W a ⊓ U i) ⊓ (W b ⊓ U i) ≤ W b ⊓ U i) (xs i b) =
        rO hle (rO (inf_le_inf_right (U i) inf_le_right) (xs i b)) := by rw [rO_rO]
    rw [e1, e2]
    exact congrArg _ h
  have hcov : ∀ i, T ⊓ U i ≤ ⨆ a, W a ⊓ U i := fun i => by rw [← iSup_inf_eq]
  have hcov2 : ∀ i j, T ⊓ (U i ⊓ U j) ≤ ⨆ a, W a ⊓ (U i ⊓ U j) := fun i j => by rw [← iSup_inf_eq]

  choose x hxg hxu using fun i => X.sheaf.existsUnique_gluing' (fun a => W a ⊓ U i) (T ⊓ U i)
    (fun a => homOfLE (inf_le_inf_right (U i) (hWT a))) (hcov i) (xs i) (hx i)

  have hxmem : ∀ i j, rO (leTi T i j) (x i) = rO (leij T i j) (c.u i j) * rO (leTj T i j) (x j) := by
    intro i j
    apply X.sheaf.eq_of_locally_eq' (fun a => W a ⊓ (U i ⊓ U j)) (T ⊓ (U i ⊓ U j))
      (fun a => homOfLE (inf_le_inf_right (U i ⊓ U j) (hWT a))) (hcov2 i j)
    intro a
    change rO (inf_le_inf_right (U i ⊓ U j) (hWT a)) (rO (leTi T i j) (x i)) =
      rO (inf_le_inf_right (U i ⊓ U j) (hWT a)) (rO (leij T i j) (c.u i j) * rO (leTj T i j) (x j))
    rw [map_mul, rO_rO, rO_rO, rO_rO]
    have ei : rO ((inf_le_inf_right (U i ⊓ U j) (hWT a)).trans (leTi T i j)) (x i : Γ(X, T ⊓ U i)) =
        rO (leTi (W a) i j) (xs i a) := by
      rw [← hxg i a]; exact (rO_rO _ _ _).symm
    have ej : rO ((inf_le_inf_right (U i ⊓ U j) (hWT a)).trans (leTj T i j)) (x j : Γ(X, T ⊓ U j)) =
        rO (leTj (W a) i j) (xs j a) := by
      rw [← hxg j a]; exact (rO_rO _ _ _).symm
    rw [ei, ej]
    exact (sf a).2 i j
  refine ⟨⟨fun i => x i, hxmem⟩, fun a => ?_, fun s hs => ?_⟩
  · apply Subtype.ext; funext i
    exact hxg i a
  · apply Subtype.ext; funext i
    exact hxu i (s.1 i) fun a => congrArg (fun p : families c (W a) => p.1 i) (hs a)

end GlueOfCocycle

variable {U : ι → X.Opens}


public theorem glueOfCocycle_sections_eq (c : UnitCocycle U) (T : X.Opens) :
    (Γ(glueOfCocycle c, T) : Type u) = GlueOfCocycle.families c T := rfl


public theorem glue_map_val (c : UnitCocycle U) {T T' : X.Opens} (h : T' ≤ T) (p : Γ(glueOfCocycle c, T)) (i : ι) :
    (((glueOfCocycle c).presheaf.map (homOfLE h).op p : Γ(glueOfCocycle c, T')) : GlueOfCocycle.families c T').1 i =
      rO (inf_le_inf_right (U i) h) ((p : GlueOfCocycle.families c T).1 i) := rfl


public theorem glue_smul_val (c : UnitCocycle U) {T : X.Opens} (g : Γ(X, T)) (p : Γ(glueOfCocycle c, T)) (i : ι) :
    ((g • p : Γ(glueOfCocycle c, T)) : GlueOfCocycle.families c T).1 i =
      rO inf_le_left g * (p : GlueOfCocycle.families c T).1 i := rfl


public theorem glueComponent_apply (c : UnitCocycle U) (T : X.Opens) (i : ι) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T i p = (p : GlueOfCocycle.families c T).1 i := rfl


public theorem glue_ext (c : UnitCocycle U) {T : X.Opens} {p q : Γ(glueOfCocycle c, T)}
    (h : ∀ i, glueComponent c T i p = glueComponent c T i q) : p = q :=
  Subtype.ext (funext h)


public theorem glueComponent_transition (c : UnitCocycle U) (T : X.Opens) (i j : ι) (p : Γ(glueOfCocycle c, T)) :
    rO (GlueOfCocycle.leTi T i j) (glueComponent c T i p) =
      rO (GlueOfCocycle.leij T i j) (c.u i j) * rO (GlueOfCocycle.leTj T i j) (glueComponent c T j p) :=
  (p : GlueOfCocycle.families c T).2 i j


public theorem glueComponent_map (c : UnitCocycle U) {T T' : X.Opens} (h : T' ≤ T) (i : ι) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T' i ((glueOfCocycle c).presheaf.map (homOfLE h).op p) =
      rO (inf_le_inf_right (U i) h) (glueComponent c T i p) := rfl


public theorem glueComponent_smul (c : UnitCocycle U) {T : X.Opens} (g : Γ(X, T)) (i : ι) (p : Γ(glueOfCocycle c, T)) :
    glueComponent c T i (g • p) = rO inf_le_left g * glueComponent c T i p := rfl


@[simp] public theorem glueComponent_glueMk (c : UnitCocycle U) (T : X.Opens) (x : ∀ i, Γ(X, T ⊓ U i))
    (hx : ∀ i j, rO (GlueOfCocycle.leTi T i j) (x i) =
      rO (GlueOfCocycle.leij T i j) (c.u i j) * rO (GlueOfCocycle.leTj T i j) (x j)) (i : ι) :
    glueComponent c T i (glueMk c T x hx) = x i := rfl


public theorem glueComponent_glueFrame (c : UnitCocycle U) (i k : ι) :
    glueComponent c (U i) k (glueFrame c i) = rO (le_of_eq (inf_comm (U i) (U k))) (c.u k i) := rfl


public theorem glueComponent_glueFrame_self (c : UnitCocycle U) (i : ι) :
    glueComponent c (U i) i (glueFrame c i) = 1 := by
  rw [glueComponent_glueFrame, c.refl, map_one]


public theorem isFrameOn_glueFrame (c : UnitCocycle U) (i : ι) : IsFrameOn (glueFrame c i) (U i) := by
  intro W hWU _

  have key : ∀ (g : Γ(X, W)) (k : ι),
      glueComponent c W k (g • (glueOfCocycle c).presheaf.map (homOfLE hWU).op (glueFrame c i)) =
        rO (inf_le_left : W ⊓ U k ≤ W) g * rO (inf_le_inf_right (U k) hWU) (rO (le_of_eq (inf_comm (U i) (U k))) (c.u k i)) :=
    fun g k => rfl
  constructor
  · intro g g' hgg'
    have h := congrArg (glueComponent c W i) hgg'
    simp only [key, rO_rO] at h
    rw [show rO ((inf_le_inf_right (U i) hWU).trans (le_of_eq (inf_comm (U i) (U i)))) (c.u i i) = 1 by
      rw [c.refl, map_one], mul_one, mul_one] at h
    exact (rO_bijective_of_le_le (inf_le_left : W ⊓ U i ≤ W) (le_inf le_rfl hWU)).1 h
  · intro p
    refine ⟨rO (le_inf le_rfl hWU : W ≤ W ⊓ U i) (glueComponent c W i p), ?_⟩
    apply glue_ext
    intro k
    rw [key, rO_rO, rO_rO]

    have hp := glueComponent_transition c W k i p

    apply (rO_bijective_of_le_le (GlueOfCocycle.leTi W k i)
      (le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans hWU)))).1
    rw [map_mul, rO_rO, rO_rO, hp, mul_comm]


public theorem map_glueFrame_eq_smul (c : UnitCocycle U) (i j : ι) :
    (glueOfCocycle c).presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (glueFrame c j) =
      c.u i j • (glueOfCocycle c).presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (glueFrame c i) := by
  apply glue_ext
  intro k
  rw [glueComponent_map, glueComponent_smul, glueComponent_map, glueComponent_glueFrame, glueComponent_glueFrame,
    rO_rO, rO_rO]

  have h := c.cocycle_le k i j (W := U i ⊓ U j ⊓ U k) (le_inf inf_le_right (inf_le_left.trans inf_le_left))
    inf_le_left (le_inf inf_le_right (inf_le_left.trans inf_le_right))
  rw [← h, mul_comm]

end AlgebraicGeometry.Scheme.Modules
