import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.SpragueGrundy
open MetaMathlibExt.SpragueGrundy


namespace MetaMathlibExt.SpragueGrundy

/--
[isP_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
lemma isP_iff
  {G : ImpartialGame}
  {p : G.Pos} :
-- imply
  IsP G p ↔ ∀ q (_ : q ∈ G.moves p), ¬ IsP G q := by
-- proof
  unfold IsP
  rw [WellFounded.fix_eq]

end MetaMathlibExt.SpragueGrundy

namespace MetaMathlibExt.SpragueGrundy

/--
[grundy_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma grundy_eq (G : ImpartialGame) (p : G.Pos) :
  grundy G p =
    mex ((G.moves p).attach.image (fun x : { q // q ∈ G.moves p } => grundy G x.val)) := by
  unfold grundy
  rw [WellFounded.fix_eq]

end MetaMathlibExt.SpragueGrundy

namespace MetaMathlibExt.SpragueGrundy

/--
[xor_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma xor_eq_zero_iff {x y : ℕ} : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have h2 : (x ^^^ y) ^^^ y = (0 : ℕ) ^^^ y := by rw [h]
    rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] at h2
  · intro h
    rw [h, Nat.xor_self]

end MetaMathlibExt.SpragueGrundy

namespace MetaMathlibExt.SpragueGrundy

/--
[sum_mem_left](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma sum_mem_left (G H : ImpartialGame) (a : G.Pos) (b : H.Pos)
  (a' : G.Pos) (h : a' ∈ G.moves a) :
  ((a', b) : (gameSum G H).Pos) ∈
    (gameSum G H).moves ((a, b) : (gameSum G H).Pos) := by
  let := G.eqDec
  let := H.eqDec
  change ((a', b) : G.Pos × H.Pos) ∈
    (G.moves a).image (fun a_1 => (a_1, b)) ∪
      (H.moves b).image (fun b_1 => (a, b_1))
  apply Finset.mem_union.mpr
  left
  exact Finset.mem_image.mpr ⟨a', h, rfl⟩

end MetaMathlibExt.SpragueGrundy

namespace MetaMathlibExt.SpragueGrundy

/--
[sum_mem_right](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma sum_mem_right (G H : ImpartialGame) (a : G.Pos) (b : H.Pos)
  (b' : H.Pos) (h : b' ∈ H.moves b) :
  ((a, b') : (gameSum G H).Pos) ∈
    (gameSum G H).moves ((a, b) : (gameSum G H).Pos) := by
  let := G.eqDec
  let := H.eqDec
  change ((a, b') : G.Pos × H.Pos) ∈
    (G.moves a).image (fun a_1 => (a_1, b)) ∪
      (H.moves b).image (fun b_1 => (a, b_1))
  apply Finset.mem_union.mpr
  right
  exact Finset.mem_image.mpr ⟨b', h, rfl⟩

end MetaMathlibExt.SpragueGrundy

namespace MetaMathlibExt.SpragueGrundy

/--
[sum_cases](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma sum_cases (G H : ImpartialGame) (a : G.Pos) (b : H.Pos)
  (q : (gameSum G H).Pos)
  (h : q ∈ (gameSum G H).moves ((a, b) : (gameSum G H).Pos)) :
  (∃ a', ∃ _ : a' ∈ G.moves a, q = ((a', b) : (gameSum G H).Pos)) ∨
    (∃ b', ∃ _ : b' ∈ H.moves b, q = ((a, b') : (gameSum G H).Pos)) := by
  let := (gameSum G H).eqDec
  have hdisj := Finset.mem_union.mp h
  cases hdisj with
  | inl hl =>
    obtain ⟨a', ha', heq⟩ := Finset.mem_image.mp hl
    exact Or.inl ⟨a', ha', heq.symm⟩
  | inr hr =>
    obtain ⟨b', hb', heq⟩ := Finset.mem_image.mp hr
    exact Or.inr ⟨b', hb', heq.symm⟩

end MetaMathlibExt.SpragueGrundy

namespace MetaMathlibExt.SpragueGrundy

/--
[IsP_sum_unfold](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma IsP_sum_unfold (G H : ImpartialGame) (a : G.Pos) (b : H.Pos) :
  IsP (gameSum G H) ((a, b) : (gameSum G H).Pos) ↔
    ∀ q (_ : q ∈ (gameSum G H).moves ((a, b) : (gameSum G H).Pos)),
      ¬ IsP (gameSum G H) q :=
  isP_iff _ _

end MetaMathlibExt.SpragueGrundy

/--
[wfRel](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma wfRel_eq
  {G : ImpartialGame} :
-- imply
  WellFounded (fun a b => a ∈ G.moves b) := by
-- proof
  apply MetaMathlibExt.SpragueGrundy.wfRel G

/--
[sprague_grundy](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/SpragueGrundy.lean)
-/
@[path]
private lemma sprague_grundy_eq
  {G : ImpartialGame} :
-- imply
  ∃ n : ℕ, Equiv G (nimHeap n) := by
-- proof
  apply MetaMathlibExt.SpragueGrundy.sprague_grundy G


-- created on 2026-10-20
-- updated on 2026-10-23
