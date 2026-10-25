/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/PrimitiveWord.lean -/

import Mathlib.Data.List.Basic
/-!
# Primitive finite words

This file formalizes the standard definition used by Fabien Durand and Julien Leroy in
*Do the Properties of an S-adic Representation Determine Factor Complexity?*
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Durand/durand2.tex>, and by Sébastien Ferenczi and
Luca Q. Zamboni in *Clustering Words and Interval Exchanges*
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Zamboni/zamboni2.tex>.
-/


namespace MetaMathlibExt

/-- A nonempty finite word is primitive if it is not a proper power of another word. -/
def IsPrimitiveWord {α : Type*} (u : List α) : Prop :=
  u ≠ [] ∧ ∀ (v : List α) (n : ℕ), List.flatten (List.replicate n v) = u → n = 1

end MetaMathlibExt
