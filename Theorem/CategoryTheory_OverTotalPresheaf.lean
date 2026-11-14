import Mathlib
import Def.CategoryTheory_OverTotalPresheaf
import Abbrev.CategoryTheory_OverTotalPresheaf

set_option autoImplicit false

open CategoryTheory Category Opposite

namespace CategoryTheory.Functor

universe w v u

variable {C : Type u} [Category.{v} C] {S : C} (G : (Over S)ᵒᵖ ⥤ Type w)

lemma map_op_apply_eq_of_left_eq {A B : Over S} (k k' : A ⟶ B) (h : k.left = k'.left) (x : G.obj (op B)) :
    G.map k.op x = G.map k'.op x := by
  rw [Over.OverMorphism.ext h]

lemma map_op_apply_eq_self {A : Over S} (k : A ⟶ A) (h : k.left = 𝟙 _) (x : G.obj (op A)) :
    G.map k.op x = x := by
  rw [show k = 𝟙 A from Over.OverMorphism.ext (by simpa using h), op_id, Functor.map_id_apply]

lemma map_op_map_op_apply {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (x : G.obj (op B')) :
    G.map k.op (G.map k'.op x) = G.map (k ≫ k').op x := by
  rw [op_comp, Functor.map_comp_apply]

lemma map_op_map_op_apply_eq_self {A B : Over S} (k : A ⟶ B) (k' : B ⟶ A) (h : (k ≫ k').left = 𝟙 _)
    (x : G.obj (op A)) : G.map k.op (G.map k'.op x) = x := by
  rw [map_op_map_op_apply]
  exact map_op_apply_eq_self _ (k ≫ k') h x

lemma map_op_map_op_map_op_apply_eq_self {A B B' : Over S} (k : A ⟶ B) (k' : B ⟶ B') (k'' : B' ⟶ A)
    (h : (k ≫ k' ≫ k'').left = 𝟙 _) (x : G.obj (op A)) : G.map k.op (G.map k'.op (G.map k''.op x)) = x := by
  rw [map_op_map_op_apply, map_op_map_op_apply]
  rw [Category.assoc k k' k'']; exact map_op_apply_eq_self _ (k ≫ k' ≫ k'') h x

lemma map_op_map_op_apply_eq {A B B' D : Over S} (k : A ⟶ B) (k' : B ⟶ B') (l : A ⟶ D) (l' : D ⟶ B')
    (h : (k ≫ k').left = (l ≫ l').left) (x : G.obj (op B')) :
    G.map k.op (G.map k'.op x) = G.map l.op (G.map l'.op x) := by
  rw [map_op_map_op_apply, map_op_map_op_apply]
  exact map_op_apply_eq_of_left_eq _ (k ≫ k') (l ≫ l') h x

lemma OverTotal.ext' {T : C} {a b : G.OverTotal T} (h₁ : a.1 = b.1)
    (h₂ : G.map (Over.homMk (𝟙 T) (by simp [h₁]) : Over.mk b.1 ⟶ Over.mk a.1).op a.2 = b.2) : a = b := by
  obtain ⟨t, x⟩ := a
  obtain ⟨t', y⟩ := b
  obtain rfl : t = t' := h₁
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and]
  dsimp only at h₂
  rw [← h₂]
  symm
  exact map_op_apply_eq_self _ _ (by
    first | rfl | simp only [Over.comp_left]) x

@[simp] lemma overTotal_map_fst {T T' : Cᵒᵖ} (φ : T ⟶ T') (a : G.overTotal.obj T) :
    (G.overTotal.map φ a).1 = φ.unop ≫ a.1 := rfl

variable {G}

lemma OverTotal.toFibre_congr (T : Over S) {b b' : G.OverTotal T.left} (h : b = b') (hb : b.1 = T.hom)
    (hb' : b'.1 = T.hom) : OverTotal.toFibre T b hb = OverTotal.toFibre T b' hb' := by
  subst h; rfl

@[simp] lemma OverTotal.ofFibre_fst (T : Over S) (x : G.obj (op T)) : (OverTotal.ofFibre T x).1 = T.hom := rfl

lemma OverTotal.toFibre_ofFibre (T : Over S) (x : G.obj (op T)) :
    OverTotal.toFibre T (OverTotal.ofFibre T x) rfl = x :=
  map_op_map_op_apply_eq_self _ _ _
    (by
      simp only [Over.comp_left]
      first | rfl | exact Category.id_comp _ | simp [Category.id_comp, Category.comp_id]) x

lemma OverTotal.ofFibre_toFibre (T : Over S) (b : G.OverTotal T.left) (hb : b.1 = T.hom) :
    OverTotal.ofFibre T (OverTotal.toFibre T b hb) = b :=
  OverTotal.ext' _ (by simpa [OverTotal.ofFibre] using hb.symm)
    (map_op_map_op_map_op_apply_eq_self _ _ _ _
      (by
        simp only [Over.comp_left]
        first | rfl | exact Category.id_comp _ | simp [Category.id_comp, Category.comp_id]) _)

lemma OverTotal.toFibre_naturality {T T' : Over S} (φ : T ⟶ T') (b : G.OverTotal T'.left) (hb : b.1 = T'.hom)
    (hb' : (G.overTotal.map φ.left.op b).1 = T.hom) :
    OverTotal.toFibre T (G.overTotal.map φ.left.op b) hb' = G.map φ.op (OverTotal.toFibre T' b hb) :=
  map_op_map_op_apply_eq _ _ _ _ _
    (by
      simp only [Over.comp_left]
      first | rfl | exact Category.id_comp _ | simp [Category.id_comp, Category.comp_id]) _

namespace RepresentableBy

variable {Y : C} (e : G.overTotal.RepresentableBy Y)

lemma overTotal_homEquiv_fst {T : C} (k : T ⟶ Y) : (e.homEquiv k).1 = k ≫ e.overTotalBase := by
  have h := e.homEquiv_comp k (𝟙 Y)
  rw [comp_id] at h
  rw [h]
  rfl

end RepresentableBy

end CategoryTheory.Functor
