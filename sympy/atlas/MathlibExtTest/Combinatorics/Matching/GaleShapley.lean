/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Matching/GaleShapley.lean -/


import sympy.atlas.Combinatorics.Matching.GaleShapley
import Lemma.Finset.Matching.GaleShapley

namespace MathlibExt.Combinatorics.Matching.GaleShapley

example {M W : Type*} (mp : MPrefs M W) (m : M) (a b : W) (h : (mp m).lt a b) :
    ¬ (mp m).lt b a :=
  asymm h

example {α : Type*} (T T' : StrictTotalOrder α) (h : ∀ a b, T.lt a b ↔ T'.lt a b) : T = T' := by
  ext a b
  exact h a b

example {M W : Type*} (mp : MPrefs M W) (wp : WPrefs M W) (μ : PerfectMatching M W) (m : M) :
    ¬ IsBlockingPair mp wp μ m (μ m) := fun h =>
  (mp m).irrefl _ ((isBlockingPair_iff mp wp μ m (μ m)).1 h).1

example (mp : MPrefs Unit Unit) (wp : WPrefs Unit Unit) : IsStable mp wp (Equiv.refl Unit) :=
  (isStable_iff mp wp _).2 fun m w h => (mp m).irrefl w ((isBlockingPair_iff mp wp _ m w).1 h).1

example (mp : MPrefs (Fin 3) (Fin 3)) (wp : WPrefs (Fin 3) (Fin 3)) :
    ∃ μ : PerfectMatching (Fin 3) (Fin 3), IsStable mp wp μ :=
  gale_shapley_exists_stable_matching rfl mp wp

example {M W : Type*} [Fintype M] [Fintype W] (hCard : Fintype.card M = Fintype.card W)
    (mp : MPrefs M W) (wp : WPrefs M W) : ∃ μ : PerfectMatching M W, IsStable mp wp μ :=
  gale_shapley_exists_stable_matching_general hCard mp wp

end MathlibExt.Combinatorics.Matching.GaleShapley
