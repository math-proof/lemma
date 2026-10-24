import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.TitsTheoremProof
open ChamberComplex AptIsCoxeterProof TitsTheoremProof


/--
[sufficient_foldings_fix_fold](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/TitsTheoremProof.lean)
-/
@[path]
lemma sufficient_foldings_fix_fold
  [DecidableEq V]
  {cc : ChamberComplex V}
  {C C' : Finset V}
-- given
  (hsf : HasSufficientFoldings cc)
  (hadj : cc.toSimplicialComplex.Adjacent C C') :
-- imply
  ∃ (f : Folding cc), C.image f.morph.toFun = C ∧ C'.image f.morph.toFun = C := by
-- proof
  obtain ⟨f, _, hfC, hfC', _, _⟩ := hsf C C' hadj
  exact ⟨f, hfC, hfC'⟩


private lemma sufficient_foldings_fold_fix
  [DecidableEq V]
  {cc : ChamberComplex V}
  {C C' : Finset V}
-- given
  (hsf : HasSufficientFoldings cc)
  (hadj : cc.toSimplicialComplex.Adjacent C C') :
-- imply
  ∃ (f' : Folding cc), C'.image f'.morph.toFun = C' ∧ C.image f'.morph.toFun = C' := by
-- proof
  obtain ⟨_, f', _, _, hf'C', hf'C⟩ := hsf C C' hadj
  exact ⟨f', hf'C', hf'C⟩


private lemma wallReflection_involutive
  [DecidableEq V]
  {cc : ChamberComplex V}
  {s : WallReflection cc} :
-- imply
  ∀ v, s.refl (s.refl v) = v :=
-- proof
  s.refl_involutive


private lemma simple_ne_one
  [DecidableEq V]
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {i : B} :
-- imply
  M.toCoxeterSystem.simple i ≠ 1 := by
-- proof
  intro h
  have := M.toCoxeterSystem.length_simple i
  rw [h, CoxeterSystem.length_one] at this
  omega


private lemma simple_inv
  [DecidableEq V]
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {i : B} :
-- imply
  (M.toCoxeterSystem.simple i)⁻¹ = M.toCoxeterSystem.simple i :=
-- proof
  M.toCoxeterSystem.inv_simple i


private lemma mul_simple_ne_self
  [DecidableEq V]
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {w : M.Group}
  {i : B} :
-- imply
  w * M.toCoxeterSystem.simple i ≠ w := by
-- proof
  intro h
  have : M.toCoxeterSystem.simple i = 1 := by
    have := mul_left_cancel (a := w) (b := M.toCoxeterSystem.simple i) (c := 1)
    rw [mul_one] at this
    exact this h
  exact simple_ne_one M i this


private lemma chamberAdjacent_left_mul
  [DecidableEq V]
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {g w w' : M.Group}
-- given
  (hadj : CoxeterComplex.ChamberAdjacent M w w') :
-- imply
  CoxeterComplex.ChamberAdjacent M (g * w) (g * w') := by
-- proof
  obtain ⟨hne, i, hi⟩ := hadj
  constructor
  · intro heq; exact hne (mul_left_cancel heq)
  · exact ⟨i, by rw [hi, mul_assoc]⟩


private lemma chamberAdjacent_mul_simple
  [DecidableEq V]
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {w : M.Group}
  {i : B} :
-- imply
  CoxeterComplex.ChamberAdjacent M w (w * M.toCoxeterSystem.simple i) := by
-- proof
  constructor
  · exact Ne.symm (mul_simple_ne_self M w i)
  · exact ⟨i, rfl⟩


private lemma galleryPath_nonempty
  [DecidableEq V]
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {w : M.Group}
  {word : List B} :
-- imply
  galleryPath M w word ≠ [] := by
-- proof
  cases word <;> simp [galleryPath]


private lemma word_gallery_isGallery
  [DecidableEq V]
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  ∀ (word : List B) (w : M.Group), CoxeterComplex.IsGallery M (galleryPath M w word) := by
-- proof
  intro word
  induction word with
  | nil => intro w; exact trivial
  | cons i rest ih =>
    intro w
    show CoxeterComplex.IsGallery M (w :: galleryPath M (w * M.toCoxeterSystem.simple i) rest)
    cases rest with
    | nil =>
      show CoxeterComplex.ChamberAdjacent M w (w * M.toCoxeterSystem.simple i) ∧ True
      exact ⟨chamberAdjacent_mul_simple M w i, trivial⟩
    | cons j rest' =>
      show CoxeterComplex.ChamberAdjacent M w (w * M.toCoxeterSystem.simple i) ∧
        CoxeterComplex.IsGallery M (galleryPath M (w * M.toCoxeterSystem.simple i) (j :: rest'))
      exact ⟨chamberAdjacent_mul_simple M w i, ih (w * M.toCoxeterSystem.simple i)⟩


private lemma galleryPath_last
  [DecidableEq V]
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B} :
-- imply
  ∀ (word : List B) (w : M.Group), (galleryPath M w word).getLast (galleryPath_nonempty M w word) = wordProduct M w word := by
-- proof
  intro word
  induction word with
  | nil => intro w; simp [galleryPath, wordProduct]
  | cons i rest ih =>
    intro w
    simp only [galleryPath, wordProduct]
    have hne : galleryPath M (w * M.toCoxeterSystem.simple i) rest ≠ [] :=
      galleryPath_nonempty M _ rest
    rw [List.getLast_cons (by exact hne)]
    exact ih (w * M.toCoxeterSystem.simple i)


-- created on 2026-10-24
