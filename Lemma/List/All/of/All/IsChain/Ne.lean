import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.ChamberComplex.Folding.Part3
open ChamberComplex ChamberComplex.Folding ChamberComplex.ReversibleFolding ChamberComplex.WallReflection
open scoped Classical


/--
[List.chain_forall_of_head](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma List.chain_forall_of_head
  [DecidableEq V]
  {R : α → α → Prop}
  {P : α → Prop}
  {l : List α}
-- given
  (hne : l ≠ [])
  (hchain : l.IsChain R)
  (hhead : P (l.head hne))
  (hprop : ∀ a b, R a b → P a → P b) :
-- imply
  ∀ x ∈ l, P x := by
-- proof
  induction l with
  | nil => exact absurd rfl hne
  | cons a tl ih =>
    intro x hx
    rw [List.mem_cons] at hx
    obtain rfl | hx := hx
    · exact hhead
    · cases tl with
      | nil => simp at hx
      | cons b rest =>
        rw [List.isChain_cons] at hchain
        obtain ⟨hrel, hchain_tl⟩ := hchain
        exact ih (List.cons_ne_nil b rest) hchain_tl
          (hprop a b (hrel b rfl) hhead) x hx
namespace ChamberComplex

namespace ChamberComplex.Folding

/--
[fixed_or_moved](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma fixed_or_moved
  [DecidableEq V]
  {X : ChamberComplex V}
  {f : Folding X}
  {C : Finset V}
-- given
  (hC : X.toSimplicialComplex.IsMaximal C) :
-- imply
  C ∈ f.fixedChambers ∨ C ∈ f.movedChambers := by
-- proof
  by_cases h : C.image f.morph.toFun = C
  · exact Or.inl ⟨hC, h⟩
  · exact Or.inr ⟨hC, h⟩

end ChamberComplex.Folding

namespace ChamberComplex.Folding

/--
[image_is_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma image_is_fixed
  [DecidableEq V]
  {X : ChamberComplex V}
  {f : Folding X}
  {C : Finset V}
-- given
  (hC : X.toSimplicialComplex.IsMaximal C) :
-- imply
  C.image f.morph.toFun ∈ f.fixedChambers := by
-- proof
  refine ⟨f.chamberMap C hC, ?_⟩
  ext v; simp only [Finset.mem_image]; constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; exact ⟨u, hu, (f.idempotent u).symm⟩
  · rintro ⟨w, hw, rfl⟩; exact ⟨f.morph.toFun w, ⟨w, hw, rfl⟩, f.idempotent w⟩

end ChamberComplex.Folding

namespace ChamberComplex.Folding

/--
[fixes_pointwise](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma fixes_pointwise
  [DecidableEq V]
  {X : ChamberComplex V}
  {f : Folding X}
  {C : Finset V}
-- given
  (hfC : C.image f.morph.toFun = C) :
-- imply
  ∀ v ∈ C, f.morph.toFun v = v := by
-- proof
  intro v hv; rw [← hfC] at hv
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hv
  exact f.idempotent u

end ChamberComplex.Folding

namespace ChamberComplex.Folding

/--
[fold_adj_to_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma fold_adj_to_self
  [DecidableEq V]
  {X : ChamberComplex V}
  {f : Folding X}
  {C D : Finset V}
-- given
  (hThin : X.IsThin)
  (hadj : X.toSimplicialComplex.Adjacent C D)
  (hfC : C.image f.morph.toFun = C)
  (hfD : D.image f.morph.toFun ≠ D) :
-- imply
  D.image f.morph.toFun = C := by
-- proof
  obtain ⟨hCmax, hDmax, hne, F, hFC, hFD⟩ := hadj
  have hfix := f.fixes_pointwise hfC
  have hfF : F.image f.morph.toFun = F := by
    ext v; simp only [Finset.mem_image]; constructor
    · rintro ⟨w, hw, rfl⟩; rwa [hfix w (hFC.1.2.2 hw)]
    · intro hv; exact ⟨v, hv, hfix v (hFC.1.2.2 hv)⟩
  have hfFfD := f.preservesFacets F D hFD
  rw [hfF] at hfFfD
  have hfDmax := f.chamberMap D hDmax
  obtain ⟨D', ⟨_, _, _⟩, hD'uniq⟩ := hThin F C hFC hCmax
  have hD'D : D = D' := hD'uniq D ⟨hne.symm, hFD, hDmax⟩
  by_contra hfD_ne_C
  have : D.image f.morph.toFun = D' :=
    hD'uniq (D.image f.morph.toFun) ⟨hfD_ne_C, hfFfD, hfDmax⟩
  rw [← hD'D] at this; exact hfD this

end ChamberComplex.Folding

namespace ChamberComplex.ReversibleFolding

/--
[halves_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma halves_disjoint
  [DecidableEq V]
  {X : ChamberComplex V}
  {rf : ReversibleFolding X}
  {C : Finset V} :
-- imply
  ¬(C ∈ rf.f.fixedChambers ∧ C ∈ rf.g.fixedChambers) := by
-- proof
  intro ⟨hf, hg⟩
  have : C ∈ rf.g.movedChambers := rf.complementary_fixed ▸ hf
  exact this.2 hg.2

end ChamberComplex.ReversibleFolding

namespace ChamberComplex

/--
[reflection_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma reflection_involutive
  [DecidableEq V]
  {X : ChamberComplex V}
  {rf : ReversibleFolding X}
-- given
  (hfg : ∀ v, rf.f.morph.toFun v = v → rf.f.morph.toFun (rf.g.morph.toFun v) = v)
  (hgf : ∀ v, rf.g.morph.toFun v = v → rf.g.morph.toFun (rf.f.morph.toFun v) = v)
  (hcover : ∀ v, rf.f.morph.toFun v = v ∨ rf.g.morph.toFun v = v) :
-- imply
  ∀ v, reflectionFun rf (reflectionFun rf v) = v := by
-- proof
  intro v; simp only [reflectionFun]
  obtain hfv | hgv := hcover v
  ·
    simp [hfv]
    by_cases hgv' : rf.f.morph.toFun (rf.g.morph.toFun v) = rf.g.morph.toFun v
    ·
      have : rf.g.morph.toFun v = v := by
        have h1 := hfg v hfv; rw [hgv'] at h1; exact h1
      simp [this, hfv]
    ·
      simp [hgv']; exact hfg v hfv
  ·
    by_cases hfv : rf.f.morph.toFun v = v
    ·
      simp [hfv, hgv]
    ·
      simp [hfv, show rf.f.morph.toFun (rf.f.morph.toFun v) = rf.f.morph.toFun v from
        rf.f.idempotent v]
      exact hgf v hgv

end ChamberComplex

namespace ChamberComplex.WallReflection

/--
[refl_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma refl_involutive
  [DecidableEq V]
  {X : ChamberComplex V}
  {s : WallReflection X} :
-- imply
  ∀ v, s.refl (s.refl v) = v :=
-- proof
  reflection_involutive s.rf s.fg_id s.gf_id s.cover

end ChamberComplex.WallReflection

namespace ChamberComplex.WallReflection

/--
[refl_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma refl_injective
  [DecidableEq V]
  {X : ChamberComplex V}
  {s : WallReflection X} :
-- imply
  Function.Injective s.refl := by
-- proof
  intro a b hab
  have := congr_arg s.refl hab
  rwa [s.refl_involutive a, s.refl_involutive b] at this

end ChamberComplex.WallReflection

namespace ChamberComplex.WallReflection

/--
[refl_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma refl_surjective
  [DecidableEq V]
  {X : ChamberComplex V}
  {s : WallReflection X} :
-- imply
  Function.Surjective s.refl :=
-- proof
  fun b => ⟨s.refl b, s.refl_involutive b⟩

end ChamberComplex.WallReflection

namespace ChamberComplex.WallReflection

/--
[refl_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma refl_bijective
  [DecidableEq V]
  {X : ChamberComplex V}
  {s : WallReflection X} :
-- imply
  Function.Bijective s.refl :=
-- proof
  ⟨s.refl_injective, s.refl_surjective⟩

end ChamberComplex.WallReflection

namespace ChamberComplex

/--
[thin_implies_atMostTwo](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/Folding.lean)
-/
@[path]
lemma thin_implies_atMostTwo
  [DecidableEq V]
  {X : ChamberComplex V}
-- given
  (hThin : X.IsThin) :
-- imply
  SimplicialComplex.AtMostTwoChambers X.toSimplicialComplex := by
-- proof
  intro F C D E hFC hCmax hFD hDmax hDne hFE hEmax hEne
  obtain ⟨D', ⟨_, _, _⟩, hD'uniq⟩ := hThin F C hFC hCmax
  have hD_eq : D = D' := hD'uniq D ⟨hDne, hFD, hDmax⟩
  have hE_eq : E = D' := hD'uniq E ⟨hEne, hFE, hEmax⟩
  rw [hD_eq, hE_eq]

end ChamberComplex


-- created on 2026-10-23
