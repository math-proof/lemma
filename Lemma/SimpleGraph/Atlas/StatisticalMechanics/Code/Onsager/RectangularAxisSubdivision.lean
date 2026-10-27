import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.RectangularAxisSubdivision.Part8
open StatMech StatMech.Onsager


/--
[onsDirectionWord_stepOf_fst_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDirectionWord_stepOf_fst_sum_eq
  {word : List (Fin 4)} :
-- imply
  ((word.map stepOf).sum).1 = (word.map ons_dirExponentX).sum := by
-- proof
  apply StatMech.Onsager.onsDirectionWord_stepOf_fst_sum word

/--
[onsDirectionWord_stepOf_snd_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDirectionWord_stepOf_snd_sum_eq
  {word : List (Fin 4)} :
-- imply
  ((word.map stepOf).sum).2 = (word.map ons_dirExponentY).sum := by
-- proof
  apply StatMech.Onsager.onsDirectionWord_stepOf_snd_sum word

/--
[onsAnisotropicDirectionWord_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_nil_eq
-- given
  (width height : ℕ) :
-- imply
  onsAnisotropicDirectionWord width height [] = [] := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_nil width height

/--
[onsAnisotropicDirectionWord_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_cons_eq
  {d : Fin 4}
  {tail : List (Fin 4)}
-- given
  (width height : ℕ) :
-- imply
  onsAnisotropicDirectionWord width height (d :: tail) = List.replicate (onsAnisotropicStepScale width height d) d ++ onsAnisotropicDirectionWord width height tail := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_cons width height d tail

/--
[onsAnisotropicStepScale_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicStepScale_zero_eq
-- given
  (width height : ℕ) :
-- imply
  onsAnisotropicStepScale width height 0 = height := by
-- proof
  apply StatMech.Onsager.onsAnisotropicStepScale_zero width height

/--
[onsAnisotropicStepScale_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicStepScale_one_eq
-- given
  (width height : ℕ) :
-- imply
  onsAnisotropicStepScale width height 1 = width := by
-- proof
  apply StatMech.Onsager.onsAnisotropicStepScale_one width height

/--
[onsAnisotropicStepScale_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicStepScale_two_eq
-- given
  (width height : ℕ) :
-- imply
  onsAnisotropicStepScale width height 2 = height := by
-- proof
  apply StatMech.Onsager.onsAnisotropicStepScale_two width height

/--
[onsAnisotropicStepScale_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicStepScale_three_eq
-- given
  (width height : ℕ) :
-- imply
  onsAnisotropicStepScale width height 3 = width := by
-- proof
  apply StatMech.Onsager.onsAnisotropicStepScale_three width height

/--
[onsAnisotropicDirectionWord_step_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_step_sum_eq
  {word : List (Fin 4)}
-- given
  (width height : ℕ) :
-- imply
  ((onsAnisotropicDirectionWord width height word).map stepOf).sum = ((height : ℤ) * ((word.map stepOf).sum).1, (width : ℤ) * ((word.map stepOf).sum).2) := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_step_sum width height word

/--
[onsAnisotropicDirectionWord_exponentX_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_exponentX_sum_eq
  {word : List (Fin 4)}
-- given
  (width height : ℕ) :
-- imply
  ((onsAnisotropicDirectionWord width height word).map ons_dirExponentX).sum = (height : ℤ) * (word.map ons_dirExponentX).sum := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_exponentX_sum width height word

/--
[onsAnisotropicDirectionWord_exponentY_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_exponentY_sum_eq
  {word : List (Fin 4)}
-- given
  (width height : ℕ) :
-- imply
  ((onsAnisotropicDirectionWord width height word).map ons_dirExponentY).sum = (width : ℤ) * (word.map ons_dirExponentY).sum := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_exponentY_sum width height word

/--
[onsAnisotropicVertexEmbed_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicVertexEmbed_injective_eq
  [NeZero width]
  [NeZero height]
-- given
  (width height : ℕ) :
-- imply
  Function.Injective (onsAnisotropicVertexEmbed width height) := by
-- proof
  apply StatMech.Onsager.onsAnisotropicVertexEmbed_injective width height

/--
[onsAnisotropicDirectionWord_preserves_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_preserves_winding_eq
  {word : List (Fin 4)}
  {mx my : ℤ}
-- given
  (width height : ℕ)
  (hx : (word.map ons_dirExponentX).sum = (width : ℤ) * mx)
  (hy : (word.map ons_dirExponentY).sum = (height : ℤ) * my) :
-- imply
  ((onsAnisotropicDirectionWord width height word).map ons_dirExponentX).sum = (width * height : ℕ) * mx ∧ ((onsAnisotropicDirectionWord width height word).map ons_dirExponentY).sum = (width * height : ℕ) * my := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_preserves_winding width height word mx my hx hy

/--
[onsDiagonalShearDirectionWord_nil](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionWord_nil_eq :
-- imply
  onsDiagonalShearDirectionWord [] = [] := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionWord_nil

/--
[onsDiagonalShearDirectionWord_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionWord_cons_eq
  {d : Fin 4}
  {tail : List (Fin 4)} :
-- imply
  onsDiagonalShearDirectionWord (d :: tail) = onsDiagonalShearDirectionBlock d ++ onsDiagonalShearDirectionWord tail := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionWord_cons d tail

/--
[onsDirectionNonUturn_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDirectionNonUturn_self_eq
  {d : Fin 4} :
-- imply
  onsDirectionNonUturn d d := by
-- proof
  apply StatMech.Onsager.onsDirectionNonUturn_self d

/--
[onsDiagonalShearDirectionBlock_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionBlock_isChain_eq
  {d : Fin 4} :
-- imply
  List.IsChain onsDirectionNonUturn (onsDiagonalShearDirectionBlock d) := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionBlock_isChain d

/--
[onsDiagonalShearDirectionBlock_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionBlock_bridge_eq
  {d e : Fin 4}
-- given
  (hde : onsDirectionNonUturn d e) :
-- imply
  ∀ a ∈ (onsDiagonalShearDirectionBlock d).getLast?, ∀ b ∈ (onsDiagonalShearDirectionBlock e).head?, onsDirectionNonUturn a b := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionBlock_bridge d e hde

/--
[onsDiagonalShearDirectionWord_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionWord_isChain_eq
  {word : List (Fin 4)}
-- given
  (hchain : List.IsChain onsDirectionNonUturn word) :
-- imply
  List.IsChain onsDirectionNonUturn (onsDiagonalShearDirectionWord word) := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionWord_isChain word hchain

/--
[onsReplicateDirection_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsReplicateDirection_isChain_eq
  {d : Fin 4}
  {n : ℕ} :
-- imply
  List.IsChain onsDirectionNonUturn (List.replicate n d) := by
-- proof
  apply StatMech.Onsager.onsReplicateDirection_isChain d n

/--
[onsReplicateDirection_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsReplicateDirection_bridge_eq
  {d e : Fin 4}
  {m n : ℕ}
-- given
  (hm : 0 < m)
  (hn : 0 < n)
  (hde : onsDirectionNonUturn d e) :
-- imply
  ∀ a ∈ (List.replicate m d).getLast?, ∀ b ∈ (List.replicate n e).head?, onsDirectionNonUturn a b := by
-- proof
  apply StatMech.Onsager.onsReplicateDirection_bridge d e m n hm hn hde

/--
[onsAnisotropicDirectionWord_isChain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_isChain_eq
  {word : List (Fin 4)}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hchain : List.IsChain onsDirectionNonUturn word) :
-- imply
  List.IsChain onsDirectionNonUturn (onsAnisotropicDirectionWord width height word) := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_isChain width height hwidth hheight word hchain

/--
[onsDiagonalShearDirectionWord_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionWord_head_eq
  {word : List (Fin 4)}
  {a : Fin 4}
-- given
  (ha : a ∈ (onsDiagonalShearDirectionWord word).head?) :
-- imply
  ∃ d ∈ word.head?, a ∈ (onsDiagonalShearDirectionBlock d).head? := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionWord_head word ha

/--
[onsDiagonalShearDirectionWord_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionWord_getLast_eq
  {word : List (Fin 4)}
  {a : Fin 4}
-- given
  (ha : a ∈ (onsDiagonalShearDirectionWord word).getLast?) :
-- imply
  ∃ d ∈ word.getLast?, a ∈ (onsDiagonalShearDirectionBlock d).getLast? := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionWord_getLast word ha

/--
[onsAnisotropicDirectionWord_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_head_eq
  {word : List (Fin 4)}
  {a : Fin 4}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (ha : a ∈ (onsAnisotropicDirectionWord width height word).head?) :
-- imply
  ∃ d ∈ word.head?, a ∈ (List.replicate (onsAnisotropicStepScale width height d) d).head? := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_head width height hwidth hheight word ha

/--
[onsAnisotropicDirectionWord_getLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_getLast_eq
  {word : List (Fin 4)}
  {a : Fin 4}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (ha : a ∈ (onsAnisotropicDirectionWord width height word).getLast?) :
-- imply
  ∃ d ∈ word.getLast?, a ∈ (List.replicate (onsAnisotropicStepScale width height d) d).getLast? := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_getLast width height hwidth hheight word ha

/--
[onsCyclicDirectionNonUturn_ofFn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsCyclicDirectionNonUturn_ofFn_eq
  {n : ℕ}
  [NeZero n]
  {dir : Fin n → Fin 4}
-- given
  (hnu : ∀ k : Fin n, onsDirectionNonUturn (dir k) (dir (k + 1))) :
-- imply
  onsCyclicDirectionNonUturn (List.ofFn dir) := by
-- proof
  apply StatMech.Onsager.onsCyclicDirectionNonUturn_ofFn dir hnu

/--
[onsCyclicDirectionNonUturn_ofFn_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsCyclicDirectionNonUturn_ofFn_apply_eq
  {n : ℕ}
  [NeZero n]
  {dir : Fin n → Fin 4}
-- given
  (hcyclic : onsCyclicDirectionNonUturn (List.ofFn dir)) :
-- imply
  ∀ k : Fin n, onsDirectionNonUturn (dir k) (dir (k + 1)) := by
-- proof
  apply StatMech.Onsager.onsCyclicDirectionNonUturn_ofFn_apply dir hcyclic

/--
[onsDirectionNonUturn_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDirectionNonUturn_comm_eq
  {d e : Fin 4} :
-- imply
  onsDirectionNonUturn d e ↔ onsDirectionNonUturn e d := by
-- proof
  apply StatMech.Onsager.onsDirectionNonUturn_comm d e

/--
[onsDirectionWordTorusDart_direction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDirectionWordTorusDart_direction_eq
  {L : ℕ}
  {word : List (Fin 4)}
  [NeZero word.length]
  {k : Fin word.length} :
-- imply
  (onsDirectionWordTorusDart L word k).2 = word.get (-k) := by
-- proof
  apply StatMech.Onsager.onsDirectionWordTorusDart_direction L word k

/--
[onsDirectionWordTorusDart_valid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDirectionWordTorusDart_valid_eq
  {L : ℕ}
  {word : List (Fin 4)}
  [NeZero word.length]
  {mx my : ℤ}
-- given
  (hdisp : (word.map stepOf).sum = ((L : ℤ) * mx, (L : ℤ) * my)) :
-- imply
  ∀ k : Fin word.length, (onsDirectionWordTorusDart L word k).1 = ons_dirStep L (onsDirectionWordTorusDart L word (k + 1)).2 (onsDirectionWordTorusDart L word (k + 1)).1 := by
-- proof
  apply StatMech.Onsager.onsDirectionWordTorusDart_valid L word mx my hdisp

/--
[onsDirectionWordTorusDart_nonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDirectionWordTorusDart_nonUturn_eq
  {L : ℕ}
  {word : List (Fin 4)}
  [NeZero word.length]
-- given
  (hcyclic : onsCyclicDirectionNonUturn word) :
-- imply
  ∀ k : Fin word.length, (onsDirectionWordTorusDart L word k).2 ≠ (onsDirectionWordTorusDart L word (k + 1)).2 + 2 := by
-- proof
  apply StatMech.Onsager.onsDirectionWordTorusDart_nonUturn L word hcyclic

/--
[onsDirectionWordTorusDart_exponentX_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDirectionWordTorusDart_exponentX_sum_eq
  {L : ℕ}
  {word : List (Fin 4)}
  [NeZero word.length] :
-- imply
  (∑ k, ons_dirExponentX (onsDirectionWordTorusDart L word k).2) = (word.map ons_dirExponentX).sum := by
-- proof
  apply StatMech.Onsager.onsDirectionWordTorusDart_exponentX_sum L word

/--
[onsDirectionWordTorusDart_exponentY_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDirectionWordTorusDart_exponentY_sum_eq
  {L : ℕ}
  {word : List (Fin 4)}
  [NeZero word.length] :
-- imply
  (∑ k, ons_dirExponentY (onsDirectionWordTorusDart L word k).2) = (word.map ons_dirExponentY).sum := by
-- proof
  apply StatMech.Onsager.onsDirectionWordTorusDart_exponentY_sum L word

/--
[onsDiagonalShearDirectionWord_cyclicNonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionWord_cyclicNonUturn_eq
  {word : List (Fin 4)}
-- given
  (hcyclic : onsCyclicDirectionNonUturn word) :
-- imply
  onsCyclicDirectionNonUturn (onsDiagonalShearDirectionWord word) := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionWord_cyclicNonUturn word hcyclic

/--
[onsAnisotropicDirectionWord_cyclicNonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsAnisotropicDirectionWord_cyclicNonUturn_eq
  {word : List (Fin 4)}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hcyclic : onsCyclicDirectionNonUturn word) :
-- imply
  onsCyclicDirectionNonUturn (onsAnisotropicDirectionWord width height word) := by
-- proof
  apply StatMech.Onsager.onsAnisotropicDirectionWord_cyclicNonUturn width height hwidth hheight word hcyclic

/--
[onsDiagonalShearDirectionBlock_step_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionBlock_step_sum_eq
  {d : Fin 4} :
-- imply
  ((onsDiagonalShearDirectionBlock d).map stepOf).sum = ((stepOf d).1 + (stepOf d).2, (stepOf d).1 - (stepOf d).2) := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionBlock_step_sum d

/--
[onsDiagonalShearDirectionWord_step_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsDiagonalShearDirectionWord_step_sum_eq
  {word : List (Fin 4)} :
-- imply
  ((onsDiagonalShearDirectionWord word).map stepOf).sum = (((word.map stepOf).sum).1 + ((word.map stepOf).sum).2, ((word.map stepOf).sum).1 - ((word.map stepOf).sum).2) := by
-- proof
  apply StatMech.Onsager.onsDiagonalShearDirectionWord_step_sum word

/--
[onsRectangularShearSubdivisionWord_cyclicNonUturn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsRectangularShearSubdivisionWord_cyclicNonUturn_eq
  {word : List (Fin 4)}
-- given
  (width height : ℕ)
  (hwidth : 0 < width)
  (hheight : 0 < height)
  (hcyclic : onsCyclicDirectionNonUturn word) :
-- imply
  onsCyclicDirectionNonUturn (onsRectangularShearSubdivisionWord width height word) := by
-- proof
  apply StatMech.Onsager.onsRectangularShearSubdivisionWord_cyclicNonUturn width height hwidth hheight word hcyclic

/--
[onsRectangularShearSubdivisionWord_preserves_deck_winding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/RectangularAxisSubdivision.lean)
-/
@[path]
private lemma onsRectangularShearSubdivisionWord_preserves_deck_winding_eq
  {word : List (Fin 4)}
  {x y : ℤ}
-- given
  (width height : ℕ)
  (hdisp : (word.map stepOf).sum = ((2 * width : ℕ) * x + (height : ℤ) * y, (2 * width : ℕ) * x - (height : ℤ) * y)) :
-- imply
  ((onsRectangularShearSubdivisionWord width height word).map ons_dirExponentX).sum = (8 * width * height : ℕ) * x ∧ ((onsRectangularShearSubdivisionWord width height word).map ons_dirExponentY).sum = (8 * width * height : ℕ) * y := by
-- proof
  apply StatMech.Onsager.onsRectangularShearSubdivisionWord_preserves_deck_winding width height word x y hdisp


-- created on 2026-10-23
