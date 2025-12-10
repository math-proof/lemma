import sympy.sets.fancyset
import sympy.core.power


class Root (α : Type _) where
  sqrt : α → α
  cubic : α → α
  quartic : α → α


notation:max (priority := 1001) "√" x:max => Root.sqrt x
notation:max "∛" x:max => Root.cubic x
notation:max "∜" x:max => Root.quartic x


noncomputable instance : Root ℝ where
  sqrt := Real.sqrt
  cubic x := x ^ (3:ℝ)⁻¹
  quartic x := x ^ (4:ℝ)⁻¹

noncomputable instance : Pow ℝ* ℝ* where
  pow x y := x.map₂ Real.rpow y

noncomputable instance : Root ℝ* where
  sqrt x := x.map Real.sqrt
  cubic x := x ^ (3:ℝ*)⁻¹
  quartic x := x ^ (4:ℝ*)⁻¹


noncomputable instance : Root ℂ where
  sqrt x := x ^ (2:ℂ)⁻¹
  cubic x := x ^ (3:ℂ)⁻¹
  quartic x := x ^ (4:ℂ)⁻¹
