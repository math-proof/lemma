import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.WeilChatelet
open ETorsorPic


namespace ETorsorPic

/--
[piMap_sub_eq_deg_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
lemma piMap_sub_eq_deg_smul
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {Q₀ Q₁ : C_pts}
  {D : C_pts →₀ ℤ} :
-- imply
  piMap Q₀ D - piMap Q₁ D = piDegreeMap D • (Q₁ -ᵥ Q₀ : E_pts) := by
-- proof
  induction D using Finsupp.induction_linear with
  | zero => simp [piMap, piDegreeMap]
  | add D₁ D₂ ih₁ ih₂ =>
    simp only [map_add]
    have : piMap Q₀ D₁ + piMap Q₀ D₂ - (piMap Q₁ D₁ + piMap Q₁ D₂) =
      (piMap Q₀ D₁ - piMap Q₁ D₁) + (piMap Q₀ D₂ - piMap Q₁ D₂) := by abel
    rw [this, ih₁, ih₂, ← add_smul]
  | single P n =>
    simp only [piMap_single, piDegreeMap_single]
    rw [← smul_sub, vsub_sub_vsub_cancel_left]

end ETorsorPic

namespace ETorsorPic

/--
[piMap_independent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
lemma piMap_independent
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {Q₀ Q₁ : C_pts}
  {D : C_pts →₀ ℤ}
-- given
  (hD : piDegreeMap D = 0) :
-- imply
  piMap Q₀ D = piMap Q₁ D := by
-- proof
  have h := piMap_sub_eq_deg_smul Q₀ Q₁ D
  rw [hD, zero_smul] at h
  exact sub_eq_zero.mp h

end ETorsorPic

namespace ETorsorPic

/--
[pic0_addEquiv_E_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
lemma pic0_addEquiv_E_mk
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {DivZero_E : Type u}
  [AddCommGroup DivZero_E]
  {data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π}
  {D : DivZero}
-- given
  (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
  (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
  (hπ_surj : Function.Surjective π) :
-- imply
  pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj (QuotientAddGroup.mk' PrincDiv D) = π D := by
-- proof
  unfold pic0_addEquiv_E
  generalize piMap_ker_eq_princDiv PrincDiv π
    (abel_jacobi_ker_le_princDiv PrincDiv π data)
    (princDiv_le_ker_pi PrincDiv π data habel_converse hfunc_field_converse) = hk
  subst hk
  simp [QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse]

end ETorsorPic

namespace ETorsorPic

/--
[pic0_addEquiv_E_map_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
lemma pic0_addEquiv_E_map_add
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {DivZero_E : Type u}
  [AddCommGroup DivZero_E]
  {data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π}
  {x y : DivZero ⧸ PrincDiv}
-- given
  (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
  (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
  (hπ_surj : Function.Surjective π) :
-- imply
  pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj (x + y) = pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj x + pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj y :=
-- proof
  map_add _ x y

end ETorsorPic

namespace ETorsorPic

/--
[pic0_addEquiv_E_map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
lemma pic0_addEquiv_E_map_zero
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {DivZero_E : Type u}
  [AddCommGroup DivZero_E]
  {data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π}
-- given
  (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
  (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E)
  (hπ_surj : Function.Surjective π) :
-- imply
  pic0_addEquiv_E PrincDiv π data habel_converse hfunc_field_converse hπ_surj 0 = 0 :=
-- proof
  map_zero _
/-- Inverse formula: $\Phi^{-1}(P)$ is the class of any preimage of $P$ under $\pi$, chosen via
the surjectivity hypothesis. -/
section ConcretePic0Iso
variable {E_pts : Type u} [AddCommGroup E_pts]
  {C_pts : Type u} [AddTorsor E_pts C_pts]
  (PrincDiv : AddSubgroup (C_pts →₀ ℤ))
  (Q₀ : C_pts)

end ETorsorPic

namespace ETorsorPic

/--
[theorem_26_17_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
lemma theorem_26_17_surjective
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts] :
-- imply
  Function.Surjective (piMap Q₀ : (C_pts →₀ ℤ) →+ E_pts) :=
-- proof
  piMap_surjective Q₀

end ETorsorPic

namespace ETorsorPic

/--
[theorem_26_17_ker_le_princDiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
lemma theorem_26_17_ker_le_princDiv
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {DivZero_E : Type u}
  [AddCommGroup DivZero_E]
  {data : EllipticCurveDivisorData E_pts (C_pts →₀ ℤ) DivZero_E PrincDiv (piMap Q₀)} :
-- imply
  (piMap Q₀).ker ≤ PrincDiv :=
-- proof
  abel_jacobi_ker_le_princDiv PrincDiv (piMap Q₀) data

end ETorsorPic

namespace ETorsorPic

/--
[theorem_26_17_princDiv_le_ker](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
lemma theorem_26_17_princDiv_le_ker
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {DivZero_E : Type u}
  [AddCommGroup DivZero_E]
  {data : EllipticCurveDivisorData E_pts (C_pts →₀ ℤ) DivZero_E PrincDiv (piMap Q₀)}
-- given
  (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
  (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
-- imply
  PrincDiv ≤ (piMap Q₀).ker :=
-- proof
  princDiv_le_ker_pi PrincDiv (piMap Q₀) data habel_converse hfunc_field_converse

end ETorsorPic

namespace ETorsorPic

/--
[theorem_26_17_independent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
lemma theorem_26_17_independent
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {Q₁ : C_pts}
  {D : C_pts →₀ ℤ}
-- given
  (hD : piDegreeMap D = 0) :
-- imply
  piMap Q₀ D = piMap Q₁ D :=
-- proof
  piMap_independent Q₀ Q₁ D hD
end ETorsorPic


/--
[piMap_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
private lemma piMap_single_eq
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {Q₀ P : C_pts}
  {n : ℤ} :
-- imply
  piMap Q₀ (Finsupp.single P n) = n • (P -ᵥ Q₀ : E_pts) := by
-- proof
  apply ETorsorPic.piMap_single Q₀ P n

/--
[piDegreeMap_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
private lemma piDegreeMap_single_eq
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {P : C_pts}
  {n : ℤ} :
-- imply
  piDegreeMap (Finsupp.single P n) = n := by
-- proof
  apply ETorsorPic.piDegreeMap_single P n

/--
[piMap_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
private lemma piMap_surjective_eq
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {Q₀ : C_pts} :
-- imply
  Function.Surjective (piMap Q₀) := by
-- proof
  apply ETorsorPic.piMap_surjective Q₀

/--
[abel_jacobi_ker_le_princDiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
private lemma abel_jacobi_ker_le_princDiv_eq
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {DivZero_E : Type u}
  [AddCommGroup DivZero_E]
  {data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π} :
-- imply
  π.ker ≤ PrincDiv := by
-- proof
  apply ETorsorPic.abel_jacobi_ker_le_princDiv data

/--
[princDiv_le_ker_pi](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
private lemma princDiv_le_ker_pi_eq
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
  {DivZero_E : Type u}
  [AddCommGroup DivZero_E]
  {data : EllipticCurveDivisorData E_pts DivZero DivZero_E PrincDiv π}
-- given
  (habel_converse : data.PrincDiv_E ≤ data.σ_E.ker)
  (hfunc_field_converse : ∀ D, D ∈ PrincDiv → data.τ D ∈ data.PrincDiv_E) :
-- imply
  PrincDiv ≤ π.ker := by
-- proof
  apply ETorsorPic.princDiv_le_ker_pi data habel_converse hfunc_field_converse

/--
[piMap_ker_eq_princDiv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/WeilChatelet.lean)
-/
@[path]
private lemma piMap_ker_eq_princDiv_eq
  {k : Type u}
  [Field k]
  {W : WeierstrassCurve k}
  [W.IsElliptic]
  {E_pts : Type u}
  [AddCommGroup E_pts]
-- given
  (hπ_ker_le : π.ker ≤ PrincDiv)
  (hπ_principal_in_ker : PrincDiv ≤ π.ker) :
-- imply
  π.ker = PrincDiv := by
-- proof
  apply ETorsorPic.piMap_ker_eq_princDiv hπ_ker_le hπ_principal_in_ker


-- created on 2026-10-23
