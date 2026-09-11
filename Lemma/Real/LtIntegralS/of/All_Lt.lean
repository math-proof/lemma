import sympy.Basic
import sympy.integrals.integrals


@[main, comm 8]
private lemma ioo
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : f ∈ ℒ¹ a b)
  (hgi : g ∈ ℒ¹ a b)
  (h : ∀ x ∈ Set.Ioo a b, g x < f x) :
-- imply
  ∫ x : ℝ in a..b, g x < ∫ x : ℝ in a..b, f x := by
-- proof
  have hpos := intervalIntegral.intervalIntegral_pos_of_pos_on (hfi.sub hgi)
    (fun x hx ↦ sub_pos.mpr (h x hx)) hab
  rw [intervalIntegral.integral_sub hfi hgi] at hpos
  exact sub_pos.mp hpos


/--
| attributes | lemma |
| :---: | :---: |
| main | Real.LtIntegralS.of.All_Lt |
| comm 8 | Real.GtIntegralS.of.All_Gt |
-/
@[main, comm 8]
private lemma main
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : f ∈ ℒ¹ a b)
  (hgi : g ∈ ℒ¹ a b)
  (h : ∀ x ∈ Set.Ioc a b, g x < f x) :
-- imply
  ∫ x : ℝ in a..b, g x < ∫ x : ℝ in a..b, f x :=
-- proof
  ioo hab hfi hgi fun x hx ↦ h x (Set.Ioo_subset_Ioc_self hx)


@[main, comm 8]
private lemma ico
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : f ∈ ℒ¹ a b)
  (hgi : g ∈ ℒ¹ a b)
  (h : ∀ x ∈ Set.Ico a b, g x < f x) :
-- imply
  ∫ x : ℝ in a..b, g x < ∫ x : ℝ in a..b, f x :=
-- proof
  ioo hab hfi hgi fun x hx ↦ h x (Set.Ioo_subset_Ico_self hx)


@[main, comm 8]
private lemma icc
  {a b : ℝ}
  {f g : ℝ → ℝ}
-- given
  (hab : a < b)
  (hfi : f ∈ ℒ¹ a b)
  (hgi : g ∈ ℒ¹ a b)
  (h : ∀ x ∈ Set.Icc a b, g x < f x) :
-- imply
  ∫ x : ℝ in a..b, g x < ∫ x : ℝ in a..b, f x :=
-- proof
  main hab hfi hgi fun x hx ↦ h x (Set.Ioc_subset_Icc_self hx)


-- created on 2019-01-28
