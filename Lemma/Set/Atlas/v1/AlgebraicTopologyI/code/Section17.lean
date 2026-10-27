import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section17.Part6
open RealProjectiveSpace
open AlgebraicTopologyI CategoryTheory
open set is open. -/


namespace RealProjectiveSpace

/--
[isOpenMap_rpn_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
lemma isOpenMap_rpn_mk
  {n : ℕ} :
-- imply
  IsOpenMap (Quotient.mk (antipodalSetoid n)) := by
-- proof
  intro U hU
  rw [isOpen_coinduced]
  change IsOpen (Quotient.mk (antipodalSetoid n) ⁻¹'
    (Quotient.mk (antipodalSetoid n) '' U))
  suffices h : Quotient.mk (antipodalSetoid n) ⁻¹'
    (Quotient.mk (antipodalSetoid n) '' U) = U ∪ sphereNeg n '' U by
    rw [h]; exact hU.union ((sphereNegHomeomorph n).isOpenMap U hU)
  ext x
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_union]
  constructor
  · rintro ⟨y, hyU, hxy⟩
    have hrel := Quotient.exact hxy
    obtain h | h := hrel
    · left; rwa [← Subtype.ext h]
    · right; exact ⟨y, hyU, Subtype.ext (by simp [sphereNeg_val, h])⟩
  · rintro (hx | ⟨y, hyU, rfl⟩)
    · exact ⟨x, hx, rfl⟩
    · exact ⟨y, hyU, Quotient.sound (Or.inr (by simp [sphereNeg_val]))⟩

end RealProjectiveSpace

namespace RealProjectiveSpace

/--
[isOpenQuotientMap_rpn_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
lemma isOpenQuotientMap_rpn_mk
  {n : ℕ} :
-- imply
  IsOpenQuotientMap (Quotient.mk (antipodalSetoid n)) :=
-- proof
  ⟨Quot.mk_surjective, continuous_quot_mk, isOpenMap_rpn_mk n⟩

end RealProjectiveSpace

namespace RealProjectiveSpace

/--
[isClosed_antipodal_rel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
lemma isClosed_antipodal_rel
  {n : ℕ} :
-- imply
  IsClosed {p : Sphere n × Sphere n | Quotient.mk (antipodalSetoid n) p.1 = Quotient.mk (antipodalSetoid n) p.2} := by
-- proof
  suffices heq : {p : Sphere n × Sphere n |
    Quotient.mk (antipodalSetoid n) p.1 = Quotient.mk (antipodalSetoid n) p.2} =
    {p | (p.1 : EuclideanSpace ℝ (Fin (n + 1))) = p.2} ∪
    {p | (p.1 : EuclideanSpace ℝ (Fin (n + 1))) = -↑p.2} by
    rw [heq]
    exact (isClosed_eq (continuous_subtype_val.comp continuous_fst)
      (continuous_subtype_val.comp continuous_snd)).union
      (isClosed_eq (continuous_subtype_val.comp continuous_fst)
        (continuous_neg.comp (continuous_subtype_val.comp continuous_snd)))
  ext ⟨x, y⟩
  simp only [Set.mem_setOf_eq, Set.mem_union]
  rw [Quotient.eq]
  rfl

end RealProjectiveSpace

namespace RealProjectiveSpace

/--
[rpn_t2Space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
lemma rpn_t2Space
  {n : ℕ} :
-- imply
  T2Space (RPn n) :=
-- proof
  (t2Space_iff_of_isOpenQuotientMap (isOpenQuotientMap_rpn_mk n)).mpr
    (isClosed_antipodal_rel n)

end RealProjectiveSpace

/--
[rpnImageSubgroup_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
private lemma rpnImageSubgroup_zero_eq
  {n : ℕ} :
-- imply
  rpnImageSubgroup n 0 = ⊥ := by
-- proof
  apply RealProjectiveSpace.rpnImageSubgroup_zero n

/--
[rpnImageSubgroup_odd_lt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
private lemma rpnImageSubgroup_odd_lt_eq
  {n k : ℕ}
-- given
  (hk : Odd k)
  (hkn : k < n) :
-- imply
  rpnImageSubgroup n k = AddSubgroup.zmultiples (2 : ℤ) := by
-- proof
  apply RealProjectiveSpace.rpnImageSubgroup_odd_lt hk hkn

/--
[rpnImageSubgroup_self](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
private lemma rpnImageSubgroup_self_eq
  {n : ℕ} :
-- imply
  rpnImageSubgroup n n = ⊥ := by
-- proof
  apply RealProjectiveSpace.rpnImageSubgroup_self n

/--
[sphereNeg_val](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
private lemma sphereNeg_val_eq
  {n : ℕ}
  {x : Sphere n} :
-- imply
  (↑(sphereNeg n x) : EuclideanSpace ℝ (Fin (n + 1))) = -↑x := by
-- proof
  apply RealProjectiveSpace.sphereNeg_val n x

/--
[sphereNeg_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
private lemma sphereNeg_involutive_eq
  {n : ℕ} :
-- imply
  Function.Involutive (sphereNeg n) := by
-- proof
  apply RealProjectiveSpace.sphereNeg_involutive n

/--
[continuous_sphereNeg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
private lemma continuous_sphereNeg_eq
  {n : ℕ} :
-- imply
  Continuous (sphereNeg n) := by
-- proof
  apply RealProjectiveSpace.continuous_sphereNeg n

/--
[rpnRawVec_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
private lemma rpnRawVec_apply_eq
  {n k : ℕ}
  {x : Fin k → ℝ}
  {i : Fin (n + 1)}
-- given
  (hk : k ≤ n) :
-- imply
  (rpnRawVec n k hk x) i = if h : (i : ℕ) < k then x ⟨i, h⟩ else if (i : ℕ) = k then 1 - ‖x‖ else 0 := by
-- proof
  apply RealProjectiveSpace.rpnRawVec_apply n k hk x i

/--
[rpnRawVec_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section17.lean)
-/
@[path]
private lemma rpnRawVec_ne_zero_eq
  {n k : ℕ}
  {x : Fin k → ℝ}
-- given
  (hk : k ≤ n) :
-- imply
  rpnRawVec n k hk x ≠ 0 := by
-- proof
  apply RealProjectiveSpace.rpnRawVec_ne_zero n k hk x


-- created on 2026-10-23
