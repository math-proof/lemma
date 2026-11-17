module

public import Mathlib
public import Structure.v1.Atlas.GeometryOfManifolds.code.Counterexamples.Part2

public section

open DifferentialFormSpace KTGamma


/--
[freeAbelianRank_Z3](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem freeAbelianRank_Z3 :
-- imply
  FreeAbelianRank.rank (G := Multiplicative ℤ × Multiplicative ℤ × Multiplicative ℤ) = 3 := by
-- proof
  rfl

/--
[KTGamma.abelianizationFreeRank_eq_three](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem KTGamma.abelianizationFreeRank_eq_three :
-- imply
  KTGamma.abelianizationFreeRank = 3 := by
-- proof
  unfold KTGamma.abelianizationFreeRank
  exact freeAbelianRank_Z3

/--
[kodaira_thurston_first_betti](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem kodaira_thurston_first_betti
  {M : KodairaThurstonManifold} :
-- imply
  M.hodge.betti 1 = 3 :=
-- proof
  M.betti_one_eq_three

/--
[kodaira_thurston_not_kahler](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem kodaira_thurston_not_kahler
  {Ω : ℕ → Type*}
  [inst : DifferentialFormSpace Ω VF]
  [hcs : IsCompactSymplectic Ω VF]
  [hbr : HasLieBracket Ω VF]
  {S : SymplecticManifold Ω VF}
  [hH : @HasHodgeNumbers Ω VF inst]
-- given
  (J : AlmostComplexStr (inst := inst))
  (hb1 : hH.betti 1 = 3) :
-- imply
  ¬ IsKahler S J := by
-- proof
  intro hK
  have ⟨m, hm⟩ := compact_kahler_odd_betti_even S J hK 1 (by norm_num)
  omega

/--
[ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem ext_eq
  {g h : KTGamma}
-- given
  (ha : g.a = h.a)
  (hb : g.b = h.b)
  (hc : g.c = h.c)
  (hd : g.d = h.d) :
-- imply
  g = h := by
-- proof
  apply KTGamma.ext ha hb hc hd

/--
[mul_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem mul_def_eq
-- given
  (g h : KTGamma) :
-- imply
  g * h = mul' g h := by
-- proof
  apply KTGamma.mul_def g h

/--
[one_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem one_def_eq :
-- imply
  (1 : KTGamma) = one' := by
-- proof
  apply KTGamma.one_def

/--
[inv_def](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem inv_def_eq
  {g : KTGamma} :
-- imply
  g⁻¹ = inv' g := by
-- proof
  apply KTGamma.inv_def g

/--
[generator3_eq_commutator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem generator3_eq_commutator_eq :
-- imply
  generator3 = mk 0 1 0 0 * mk 0 0 0 1 * (mk 0 1 0 0)⁻¹ * (mk 0 0 0 1)⁻¹ := by
-- proof
  apply KTGamma.generator3_eq_commutator

/--
[of_generator3_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem of_generator3_eq_one_eq :
-- imply
  Abelianization.of generator3 = 1 := by
-- proof
  apply KTGamma.of_generator3_eq_one

/--
[of_c_component_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem of_c_component_trivial_eq
  {c : ℤ} :
-- imply
  Abelianization.of (mk 0 0 c 0) = (1 : Abelianization KTGamma) := by
-- proof
  apply KTGamma.of_c_component_trivial c

/--
[of_eq_of_drop_c](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem of_eq_of_drop_c_eq
  {a b c d : ℤ} :
-- imply
  Abelianization.of (mk a b c d) = Abelianization.of (mk a b 0 d) := by
-- proof
  apply KTGamma.of_eq_of_drop_c a b c d

/--
[liftedProj_sectionHom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem liftedProj_sectionHom_eq :
-- imply
  liftedProj.comp sectionHom = MonoidHom.id _ := by
-- proof
  apply KTGamma.liftedProj_sectionHom

/--
[sectionHom_liftedProj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/Counterexamples.lean)
-/
public theorem sectionHom_liftedProj_eq :
-- imply
  sectionHom.comp liftedProj = MonoidHom.id _ := by
-- proof
  apply KTGamma.sectionHom_liftedProj


-- created on 2026-10-23
