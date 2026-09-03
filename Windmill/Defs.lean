-- Let S be a set of at least two points in the plane.
-- Assume that no three points are collinear.

import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic

open scoped InnerProductSpace

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

noncomputable def oangle_btw (p q : Point) (_ : p ≠ 0) (_ : q ≠ 0) : Real.Angle :=
  Orientation.oangle Point.orientation p q

noncomputable def oangle (p : Point) (h : p ≠ 0) : Real.Angle :=
  oangle_btw (Point.mk 1 0) p (by simp) h

noncomputable def fromAngle (θ : Real.Angle) : Point := Point.mk θ.cos θ.sin

noncomputable def rot (p : Point) (θ : Real.Angle) : Point :=
  mk (p.x * θ.cos - p.y * θ.sin) (p.x * θ.sin + p.y * θ.cos)

-- simp theorems

@[simp]
theorem simp_mk_x {x y : ℝ} : (mk x y).x = x := by rfl
@[simp]
theorem simp_mk_y {x y : ℝ} : (mk x y).y = y := by rfl

@[simp]
theorem simp_mk_smul {s x y : ℝ} : s • Point.mk x y = Point.mk (s * x) (s * y) := by
  unfold mk
  change s • !₂[x, y] = !₂[s * x, s * y]
  ext i
  fin_cases i <;> simp

-- angle theorems

theorem x_eq_rcosθ (p : Point) (h : p ≠ 0) : p.x = ‖p‖ * (p.oangle h).cos := by
  sorry

theorem y_eq_rsinθ (p : Point) (h : p ≠ 0) : p.y = ‖p‖ * (p.oangle h).sin := by
  sorry

end Point

#min_imports
