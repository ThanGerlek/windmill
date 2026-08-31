-- Let S be a set of at least two points in the plane.
-- Assume that no three points are collinear.

import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
open scoped InnerProductSpace

-- structure Point where
--   x : ℝ
--   y : ℝ

abbrev Point := EuclideanSpace ℝ (Fin 2)

namespace Point

abbrev mk (x y : ℝ) : Point := !₂[x, y]

abbrev x (p : Point) : ℝ := p 0
abbrev y (p : Point) : ℝ := p 1

noncomputable abbrev dot (p q : Point) : ℝ := ⟪p, q⟫_ℝ

noncomputable def hat (p : Point) (hn0 : p ≠ 0) : {p_hat : Point // ‖p_hat‖ = 1} :=
  ⟨‖p‖⁻¹ • p,
    by exact @norm_smul_inv_norm ℝ (inferInstance) Point (inferInstance) (inferInstance) p hn0⟩

-- angle and oangle

instance instPointFinrankFact : Fact (Module.finrank ℝ Point = 2) := ⟨finrank_euclideanSpace_fin⟩

noncomputable def orientation : Orientation ℝ Point (Fin 2) :=
  (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation

noncomputable def oangle (p q : Point) : Real.Angle := Orientation.oangle Point.orientation p q

noncomputable def angle (p q : Point) : Real.Angle := InnerProductGeometry.angle p q

-- theorems

theorem inner_eq_cos_angle_of_norm_eq_one {x y : Point} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
: x.dot y = Real.cos (InnerProductGeometry.angle x y) :=
  InnerProductGeometry.inner_eq_cos_angle_of_norm_eq_one hx hy

@[simp]
theorem inner_eq_norm_mul_norm_mul_cos_oangle (x y : Point)
: x.dot y = ‖x‖ * ‖y‖ * (x.oangle y).cos := by
  let h := Orientation.inner_eq_norm_mul_norm_mul_cos_oangle Point.orientation x y
  change x.dot y = ‖x‖ * ‖y‖ * (x.oangle y).cos at h
  exact h

end Point

variable (v w : Point)

#min_imports
