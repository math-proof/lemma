import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.GroupTheory.FiniteGroupConvolution
open scoped BigOperators
open MathlibExt.GroupTheory.FiniteGroupConvolutionWanted


/--
[conv_assoc_inner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_assoc_inner
  [Group G]
  [Fintype G]
  {g h : G → ℂ}
  {z x : G} :
-- imply
  (∑ y : G, g (z⁻¹ * y) * h (y⁻¹ * x)) =
    ∑ w : G, g w * h (w⁻¹ * (z⁻¹ * x)) := by
-- proof
  symm
  refine Fintype.sum_equiv (Equiv.mulLeft z) _ _ fun w => ?_
  simp [mul_assoc]

/--
[conv_assoc_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_assoc_apply
  [Group G]
  [Fintype G]
  {f g h : G → ℂ}
  {x : G} :
-- imply
  conv (conv f g) h x = conv f (conv g h) x := by
-- proof
  simp only [conv]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum, conv_assoc_inner]

/--
[conv_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_assoc
  [Group G]
  [Fintype G]
  {f g h : G → ℂ} :
-- imply
  conv (conv f g) h = conv f (conv g h) := by
-- proof
  funext x
  apply conv_assoc_apply

/--
[conv_single_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_single_one_apply
  [Group G]
  [Fintype G]
  [DecidableEq G]
  {f : G → ℂ}
  {x : G} :
-- imply
  conv (Pi.single (1 : G) (1 : ℂ)) f x = f x := by
-- proof
  simp [conv, Pi.single_apply]

/--
[conv_single_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_single_one
  [Group G]
  [Fintype G]
  [DecidableEq G]
  {f : G → ℂ} :
-- imply
  conv (Pi.single (1 : G) (1 : ℂ)) f = f := by
-- proof
  funext x
  apply conv_single_one_apply

/--
[conv_comm_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_comm_apply
  [CommGroup G]
  [Fintype G]
  {f g : G → ℂ}
  {x : G} :
-- imply
  conv f g x = conv g f x := by
-- proof
  simp only [conv]
  refine Fintype.sum_equiv ((Equiv.inv G).trans (Equiv.mulRight x)) _ _ fun y => ?_
  simp [mul_comm]

/--
[conv_comm_of_comm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_comm_of_comm
  [CommGroup G]
  [Fintype G]
  {f g : G → ℂ} :
-- imply
  conv f g = conv g f := by
-- proof
  funext x
  apply conv_comm_apply

/--
[conv_charPair_inner](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_charPair_inner
  [Group G]
  [Fintype G]
  {φ : G →* ℂ}
  {g : G → ℂ}
  {y : G} :
-- imply
  (∑ x : G, φ x * g (y⁻¹ * x)) = φ y * ∑ z : G, φ z * g z := by
-- proof
  rw [← Equiv.sum_comp (Equiv.mulLeft y)]
  simp [map_mul, Finset.mul_sum, mul_assoc]

/--
[conv_charPair_apply](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma conv_charPair_apply
  [Group G]
  [Fintype G]
  {φ : G →* ℂ}
  {f g : G → ℂ} :
-- imply
  (∑ x : G, φ x * conv f g x) =
    (∑ x : G, φ x * f x) * (∑ x : G, φ x * g x) := by
-- proof
  simp only [conv]
  rw [Fintype.sum_mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  calc
    _ = f y * ∑ x : G, φ x * g (y⁻¹ * x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ac_rfl
    _ = f y * (φ y * ∑ z : G, φ z * g z) := by
      rw [conv_charPair_inner]
    _ = ∑ z : G, (φ y * f y) * (φ z * g z) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ac_rfl

/--
[charPair_conv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteGroupConvolution.lean)
-/
@[path]
private lemma charPair_conv
  [Group G]
  [Fintype G]
  {φ : G →* ℂ}
  {f g : G → ℂ} :
-- imply
  (∑ x : G, φ x * conv f g x) =
    (∑ x : G, φ x * f x) * (∑ x : G, φ x * g x) := by
-- proof
  apply conv_charPair_apply


-- created on 2026-10-20
-- updated on 2026-10-26
