import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.FundamentalThm.Part5
open CategoryTheory Category Limits ChainComplex HomologicalComplex FundamentalThm FundamentalThm.Resolution


namespace FundamentalThm.Resolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Z : C}
/--
[complex_d_comp_π_f_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
vanishes, since the augmentation is a chain map into the complex concentrated in degree zero. -/
@[simp]
lemma complex_d_comp_π_f_zero (Q : Resolution Z) :
  Q.complex.d 1 0 ≫ Q.π.f 0 = 0 := by
  rw [← Q.π.comm 1 0, single_obj_d, comp_zero]

end FundamentalThm.Resolution

namespace FundamentalThm.Resolution

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {Z : C}
/--
[exact₀](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
lemma exact₀ (Q : Resolution Z) :
  (ShortComplex.mk (Q.complex.d 1 0) (Q.π.f 0) Q.complex_d_comp_π_f_zero).Exact := by
  have : (ShortComplex.mk (Q.complex.d 1 0) (Q.π.f 0)
    Q.complex_d_comp_π_f_zero).HasHomology := inferInstance
  exact ShortComplex.exact_of_g_is_cokernel _ Q.isColimitCokernelCofork
set_option backward.isDefEq.respectTransparency false in

end FundamentalThm.Resolution

namespace FundamentalThm.Resolution

/--
[complex_exactAt_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
lemma complex_exactAt_succ
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Z : C}
  {Q : Resolution Z}
  {n : ℕ} :
-- imply
  Q.complex.ExactAt (n + 1) := by
-- proof
  rw [← quasiIsoAt_iff_exactAt' Q.π (n + 1) (exactAt_succ_single_obj _ _)]
  infer_instance

end FundamentalThm.Resolution

namespace FundamentalThm.Resolution

/--
[exact_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
lemma exact_succ
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Z : C}
  {Q : Resolution Z}
  {n : ℕ} :
-- imply
  (ShortComplex.mk _ _ (Q.complex.d_comp_d (n + 2) (n + 1) n)).Exact :=
-- proof
  ((HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n)
    (by simp only [prev]; rfl) (by simp)).1 (Q.complex_exactAt_succ n)
set_option backward.isDefEq.respectTransparency false in

end FundamentalThm.Resolution

namespace FundamentalThm

/--
[liftHomotopyZeroOne_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
lemma liftHomotopyZeroOne_comp
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Y Z : C}
  {P : ProjectiveResolution Y}
  {Q : Resolution Z}
  {f : P.complex ⟶ Q.complex}
-- given
  (comm : f ≫ Q.π = 0) :
-- imply
  liftHomotopyZeroOne f comm ≫ Q.complex.d 2 1 = f.f 1 - P.complex.d 1 0 ≫ liftHomotopyZeroZero f comm :=
-- proof
  (Q.exact_succ 0).liftFromProjective_comp _ _

end FundamentalThm

namespace FundamentalThm

/--
[liftHomotopyZeroSucc_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
lemma liftHomotopyZeroSucc_comp
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Y Z : C}
  {P : ProjectiveResolution Y}
  {Q : Resolution Z}
  {f : P.complex ⟶ Q.complex}
  {n : ℕ}
  {g : P.complex.X n ⟶ Q.complex.X (n + 1)}
  {g' : P.complex.X (n + 1) ⟶ Q.complex.X (n + 2)}
-- given
  (w : f.f (n + 1) = P.complex.d (n + 1) n ≫ g + g' ≫ Q.complex.d (n + 2) (n + 1)) :
-- imply
  liftHomotopyZeroSucc f n g g' w ≫ Q.complex.d (n + 3) (n + 2) = f.f (n + 2) - P.complex.d _ _ ≫ g' :=
-- proof
  (Q.exact_succ (n + 1)).liftFromProjective_comp _ _

end FundamentalThm

/--
[complex_d_comp_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
private lemma complex_d_comp__eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Z : C}
  {Q : Resolution Z} :
-- imply
  Q.complex.d 1 0 ≫ Q.π.f 0 = 0 := by
-- proof
  apply FundamentalThm.Resolution.complex_d_comp_ Q

/--
[exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
private lemma exact_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Z : C}
  {Q : Resolution Z} :
-- imply
  (ShortComplex.mk (Q.complex.d 1 0) (Q.π.f 0) Q.complex_d_comp_π_f_zero).Exact := by
-- proof
  apply FundamentalThm.Resolution.exact Q

/--
[liftFOne_zero_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
private lemma liftFOne_zero_comm_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Y Z : C}
  {f : Y ⟶ Z}
  {P : ProjectiveResolution Y}
  {Q : Resolution Z} :
-- imply
  liftFOne f P Q ≫ Q.complex.d 1 0 = P.complex.d 1 0 ≫ liftFZero f P Q := by
-- proof
  apply FundamentalThm.liftFOne_zero_comm f P Q

/--
[lift_commutes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
private lemma lift_commutes_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Y Z : C}
  {f : Y ⟶ Z}
  {P : ProjectiveResolution Y}
  {Q : Resolution Z} :
-- imply
  lift f P Q ≫ Q.π = P.π ≫ (ChainComplex.single₀ C).map f := by
-- proof
  apply FundamentalThm.lift_commutes f P Q

/--
[liftHomotopyZeroZero_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/FundamentalThm.lean)
-/
@[path]
private lemma liftHomotopyZeroZero_comp_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {Y Z : C}
  {P : ProjectiveResolution Y}
  {Q : Resolution Z}
  {f : P.complex ⟶ Q.complex}
-- given
  (comm : f ≫ Q.π = 0) :
-- imply
  liftHomotopyZeroZero f comm ≫ Q.complex.d 1 0 = f.f 0 := by
-- proof
  apply FundamentalThm.liftHomotopyZeroZero_comp f comm


-- created on 2026-10-23
