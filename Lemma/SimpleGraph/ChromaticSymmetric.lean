import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.SimpleGraph.ChromaticSymmetric
open SimpleGraph


namespace SimpleGraph

/--
[SameChromaticSymmetricFunction.refl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean)
-/
@[path]
lemma SameChromaticSymmetricFunction.refl
  [Finite V]
  {G : SimpleGraph V} :
-- imply
  SameChromaticSymmetricFunction G G :=
-- proof
  fun _ _ => rfl

end SimpleGraph

namespace SimpleGraph

/--
[SameChromaticSymmetricFunction.symm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean)
-/
@[path]
lemma SameChromaticSymmetricFunction.symm
  [Finite V] [Finite W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
-- given
  (h : SameChromaticSymmetricFunction G H) :
-- imply
  SameChromaticSymmetricFunction H G :=
-- proof
  fun k multiplicity => (h k multiplicity).symm

end SimpleGraph

namespace SimpleGraph

/--
[SameChromaticSymmetricFunction.trans](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean)
-/
@[path]
lemma SameChromaticSymmetricFunction.trans
  [Finite V] [Finite W] [Finite U]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  {K : SimpleGraph U}
-- given
  (hGH : SameChromaticSymmetricFunction G H)
  (hHK : SameChromaticSymmetricFunction H K) :
-- imply
  SameChromaticSymmetricFunction G K :=
-- proof
  fun k multiplicity => (hGH k multiplicity).trans (hHK k multiplicity)

end SimpleGraph

namespace SimpleGraph

/--
[SameChromaticSymmetricFunction.of_iso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean)
-/
@[path]
lemma SameChromaticSymmetricFunction.of_iso
  [Finite V] [Finite W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
-- given
  (e : G ≃g H) :
-- imply
  SameChromaticSymmetricFunction G H := by
-- proof
  intro k multiplicity
  classical
  let F : G.Coloring (Fin k) → H.Coloring (Fin k) := fun c => c.comap e.symm.toHom
  let B : H.Coloring (Fin k) → G.Coloring (Fin k) := fun d => d.comap e.toHom
  have hBF : ∀ c, B (F c) = c := fun c => by
    ext v
    simp [F, B, Coloring.comap]
  have hFB : ∀ d, F (B d) = d := fun d => by
    ext w
    simp [F, B, Coloring.comap]
  have hfib : ∀ (c : G.Coloring (Fin k)) (color : Fin k),
    Nat.card { w : W // F c w = color } = Nat.card { v : V // c v = color } := by
    intro c color
    apply Nat.card_congr
    refine
      { toFun := fun w => ⟨e.symm w, w.property⟩
        invFun := fun v => ⟨e v, by simpa [F, Coloring.comap] using v.property⟩
        left_inv := fun w => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
  apply Nat.card_congr
  refine Equiv.subtypeEquiv ⟨F, B, hBF, hFB⟩ (fun c => ?_)
  simp only [Equiv.coe_fn_mk]
  constructor
  · intro h color
    rw [hfib c color]
    exact h color
  · intro h color
    rw [← hfib c color]
    exact h color

end SimpleGraph


-- created on 2026-10-20
-- updated on 2026-10-23
