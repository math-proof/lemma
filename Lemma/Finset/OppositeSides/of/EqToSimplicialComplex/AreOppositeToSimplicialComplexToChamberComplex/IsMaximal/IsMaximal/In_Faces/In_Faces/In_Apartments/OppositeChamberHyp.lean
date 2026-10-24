import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.OppositeChambers
open scoped Classical


/--
[wall_separates_opposite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/OppositeChambers.lean)
-/
@[path]
lemma wall_separates_opposite
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C D : Finset V}
  {cc : ChamberComplex V}
  {f : ChamberComplex.Folding cc}
-- given
  (hyp : OppositeChamberHyp b)
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : C ∈ A.faces)
  (hD : D ∈ A.faces)
  (hCmax : A.IsMaximal C)
  (hDmax : A.IsMaximal D)
  (hopp : AreOpposite b.toChamberComplex.toSimplicialComplex C D)
  (hcc : cc.toSimplicialComplex = A) :
-- imply
  ChamberComplex.OppositeSides f C D := by
-- proof
  by_contra h_not_opp
  have hCfm : C.image f.morph.toFun = C ∨ C.image f.morph.toFun ≠ C := em _
  have hDfm : D.image f.morph.toFun = D ∨ D.image f.morph.toFun ≠ D := em _
  have h_neg : ¬(C.image f.morph.toFun = C ∧ D.image f.morph.toFun ≠ D) ∧
    ¬(D.image f.morph.toFun = D ∧ C.image f.morph.toFun ≠ C) := by
    constructor <;> intro h <;> exact h_not_opp (by unfold ChamberComplex.OppositeSides; tauto)
  obtain ⟨f', hcompl, hrev⟩ := hyp.apt_reversible_foldings A hA cc hcc f
  have hCmax_cc : cc.toSimplicialComplex.IsMaximal C := hcc ▸ hCmax
  have hDmax_cc : cc.toSimplicialComplex.IsMaximal D := hcc ▸ hDmax
  obtain hfC | hfC <;> rcases hDfm with hfD | hfD := hCfm
  ·
    have hf'D_moved : D.image f'.morph.toFun ≠ D := (hcompl D hDmax_cc).mp hfD
    have hff'D : (D.image f'.morph.toFun).image f.morph.toFun = D :=
      hrev D hDmax_cc hfD
    have hf'D_max := hyp.fold_preserves_maximal A hA cc hcc f' D hDmax_cc
    have hf_moves_f'D : (D.image f'.morph.toFun).image f.morph.toFun ≠
      D.image f'.morph.toFun := by rw [hff'D]; exact hf'D_moved.symm
    have hdist_lt := hyp.fold_decreases_dist A hA cc hcc f
      C (D.image f'.morph.toFun) hCmax_cc hf'D_max hfC hf_moves_f'D
    rw [hff'D] at hdist_lt
    have hf'D_in_A : D.image f'.morph.toFun ∈ A.faces := hcc ▸ hf'D_max.1
    have hdist_CD := hyp.apt_dist_eq A hA C D hC hD hCmax hDmax
    have hdist_Cf'D := hyp.apt_dist_eq A hA C (D.image f'.morph.toFun)
      hC hf'D_in_A hCmax (hcc ▸ hf'D_max)
    have heq_CD : galleryDist cc.toSimplicialComplex C D = galleryDist A C D :=
      congr_arg (fun s => galleryDist s C D) hcc
    have heq_Cf'D : galleryDist cc.toSimplicialComplex C (D.image f'.morph.toFun) =
      galleryDist A C (D.image f'.morph.toFun) :=
      congr_arg (fun s => galleryDist s C (D.image f'.morph.toFun)) hcc
    rw [heq_CD, heq_Cf'D] at hdist_lt
    rw [hdist_CD, hdist_Cf'D] at hdist_lt
    set f'D := D.image f'.morph.toFun with hf'D_def
    have hf'D_max_A : A.IsMaximal f'D := by
      change A.IsMaximal f'D
      have h : cc.toSimplicialComplex.IsMaximal f'D := hf'D_max
      rwa [hcc] at h
    have hf'D_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A hA _ hf'D_max_A
    have hle := hopp.2.2 C (D.image f'.morph.toFun) hopp.1 hf'D_bmax
    exact Nat.not_lt.mpr hle hdist_lt
  ·
    exact absurd (Or.inl ⟨hfC, hfD⟩ : ChamberComplex.OppositeSides f C D) h_not_opp
  ·
    exact absurd (Or.inr ⟨hfD, hfC⟩ : ChamberComplex.OppositeSides f C D) h_not_opp
  ·
    have hf'C : C.image f'.morph.toFun = C := by
      by_contra h; exact hfC ((hcompl C hCmax_cc).mpr h)
    have hf'D : D.image f'.morph.toFun = D := by
      by_contra h; exact hfD ((hcompl D hDmax_cc).mpr h)
    obtain ⟨f'', hcompl', hrev'⟩ := hyp.apt_reversible_foldings A hA cc hcc f'
    have hf''C_moved : C.image f''.morph.toFun ≠ C := (hcompl' C hCmax_cc).mp hf'C
    have hf'f''C : (C.image f''.morph.toFun).image f'.morph.toFun = C :=
      hrev' C hCmax_cc hf'C
    have hf''C_max := hyp.fold_preserves_maximal A hA cc hcc f'' C hCmax_cc
    have hf'_moves : (C.image f''.morph.toFun).image f'.morph.toFun ≠
      C.image f''.morph.toFun := by rw [hf'f''C]; exact hf''C_moved.symm
    have hdist_lt := hyp.fold_decreases_dist A hA cc hcc f'
      D (C.image f''.morph.toFun) hDmax_cc hf''C_max hf'D hf'_moves
    rw [hf'f''C] at hdist_lt
    have hf''C_in_A : C.image f''.morph.toFun ∈ A.faces := hcc ▸ hf''C_max.1
    have hdist_DC := hyp.apt_dist_eq A hA D C hD hC hDmax hCmax
    have hdist_Df''C := hyp.apt_dist_eq A hA D (C.image f''.morph.toFun)
      hD hf''C_in_A hDmax (hcc ▸ hf''C_max)
    have heq_DC : galleryDist cc.toSimplicialComplex D C = galleryDist A D C :=
      congr_arg (fun s => galleryDist s D C) hcc
    have heq_Df''C : galleryDist cc.toSimplicialComplex D (C.image f''.morph.toFun) =
      galleryDist A D (C.image f''.morph.toFun) :=
      congr_arg (fun s => galleryDist s D (C.image f''.morph.toFun)) hcc
    rw [heq_DC, heq_Df''C] at hdist_lt
    rw [hdist_DC, hdist_Df''C] at hdist_lt
    set f''C := C.image f''.morph.toFun with hf''C_def
    have hf''C_max_A : A.IsMaximal f''C := by
      change A.IsMaximal f''C
      have h : cc.toSimplicialComplex.IsMaximal f''C := hf''C_max
      rwa [hcc] at h
    have hf''C_bmax := b.apartmentSystem.maximal_in_apt_is_maximal A hA _ hf''C_max_A
    have hopp' := areOpposite_symm hopp
    have hle := hopp'.2.2 D (C.image f''.morph.toFun) hopp'.1 hf''C_bmax
    exact Nat.not_lt.mpr hle hdist_lt

private lemma chamber_in_minimal_gallery_of_opposite
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C D : Finset V}
  {cc : ChamberComplex V}
  {C' : Finset V}
-- given
  (hyp : OppositeChamberHyp b)
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : C ∈ A.faces)
  (hD : D ∈ A.faces)
  (hCmax : A.IsMaximal C)
  (hDmax : A.IsMaximal D)
  (hopp : AreOpposite b.toChamberComplex.toSimplicialComplex C D)
  (hcc : cc.toSimplicialComplex = A)
  (hC' : C' ∈ A.faces)
  (hC'max : A.IsMaximal C') :
-- imply
  ∃ (g : Gallery b.toChamberComplex.toSimplicialComplex), g.Connects C D ∧ g.length = galleryDist b.toChamberComplex.toSimplicialComplex C D ∧ C' ∈ g.chambers := by
-- proof
  have h_all_sep : ∀ (f : ChamberComplex.Folding cc),
    ChamberComplex.OppositeSides f C D :=
    fun f => wall_separates_opposite hyp A hA C D hC hD hCmax hDmax hopp cc hcc f
  have h_add := hyp.wall_sep_additive_dist A hA cc hcc C D C'
    (hcc ▸ hCmax) (hcc ▸ hDmax) (hcc ▸ hC'max) h_all_sep
  have hdCD := hyp.apt_dist_eq A hA C D hC hD hCmax hDmax
  have hdCC' := hyp.apt_dist_eq A hA C C' hC hC' hCmax hC'max
  have hdC'D := hyp.apt_dist_eq A hA C' D hC' hD hC'max hDmax
  rw [← hcc] at hdCD hdCC' hdC'D
  rw [hdCD, hdCC', hdC'D] at h_add
  have hCbmax := b.apartmentSystem.maximal_in_apt_is_maximal A hA C hCmax
  have hC'bmax := b.apartmentSystem.maximal_in_apt_is_maximal A hA C' hC'max
  have hDbmax := b.apartmentSystem.maximal_in_apt_is_maximal A hA D hDmax
  exact hyp.gallery_through_chamber C C' D hCbmax hC'bmax hDbmax h_add


-- created on 2026-10-24
