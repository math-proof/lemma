import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.FiniteGroupConvolution
open scoped BigOperators
open MathlibExt.GroupTheory.FiniteGroupConvolutionWanted


/--
[conv_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_assoc_eq
  [Group G] [Fintype G]
  {f g h : G → ℂ} :
-- imply
  conv (conv f g) h = conv f (conv g h) := by
-- proof
  apply MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv_assoc f g h

/--
[conv_single_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_single_one_eq
  [Group G] [Fintype G] [DecidableEq G]
  {f : G → ℂ} :
-- imply
  conv (Pi.single (1 : G) (1 : ℂ)) f = f := by
-- proof
  apply MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv_single_one f

/--
[conv_comm_of_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_comm_of_comm_eq
  [CommGroup G] [Fintype G]
  {f g : G → ℂ} :
-- imply
  conv f g = conv g f := by
-- proof
  apply MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.conv_comm_of_comm f g

/--
[charPair_conv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma charPair_conv_eq
  [Group G] [Fintype G]
  {φ : G →* ℂ}
  {f g : G → ℂ} :
-- imply
  (∑ x : G, φ x * conv f g x) =
    (∑ x : G, φ x * f x) * (∑ x : G, φ x * g x) := by
-- proof
  apply MathlibExt.GroupTheory.FiniteGroupConvolutionWanted.charPair_conv φ f g


-- created on 2026-10-20
