-- Let S be a set of at least two points in the plane.
-- Assume that no three points are collinear.

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

structure Point where
  x : ℝ
  y : ℝ

structure Dir where
  x : ℝ
  y : ℝ
  normed : x^2 + y^2 = 1

namespace Dir

@[simp]
def IsVert (d : Dir) : Prop := d.x = 0
noncomputable instance (d : Dir) : Decidable d.IsVert := by unfold IsVert; infer_instance

noncomputable def to_slope (d : Dir) : Option ℝ :=
  if d.x = 0 then none else (some (d.y / d.x))

noncomputable def to_angle (d : Dir) : Real.Angle :=
  if d.x = 0 then
    if d.y ≥ 0 then (Real.pi / 2 : ℝ) else (-Real.pi / 2 : ℝ)
  --else Real.arctan (d.y / d.x) + (if d.x < 0 then Real.pi else 0)
  else if d.x < 0 then
    Real.arctan (d.y / d.x) + Real.pi
  else
    Real.arctan (d.y / d.x)

noncomputable def from_angle (θ : Real.Angle) : Dir :=
  if θ.toReal = Real.pi / 2 then Dir.mk 0 1 (by simp)
  else if θ.toReal = -Real.pi / 2 then Dir.mk 0 (-1) (by simp)
  else Dir.mk (Real.Angle.cos θ) (Real.Angle.sin θ) (by simp)

noncomputable instance : Coe Dir Real.Angle := ⟨to_angle⟩

noncomputable instance : Inhabited Dir := ⟨Dir.mk 1 0 (by simp)⟩

-- lemmas for to_from_angle

lemma angle_arctan_tan {θ : Real.Angle}
(h_range : -(Real.pi / 2) < θ.toReal ∧ θ.toReal < Real.pi / 2)
: ↑(Real.arctan (Real.Angle.tan θ)) = θ := by
  have arctan_tan := Real.arctan_tan h_range.left h_range.right
  rw [←Real.Angle.tan_toReal]
  rw [arctan_tan]
  simp

lemma tan_add_real_2_pi {θr : ℝ} : Real.tan (θr + (2:ℝ) * Real.pi) = Real.tan θr := by
  change Real.tan (θr + (2 : ℤ) * Real.pi) = Real.tan θr
  rw [Real.tan_add_int_mul_pi θr 2]

lemma angle_arctan_tan_pi {θ : Real.Angle}
(h_range : θ.toReal < -(Real.pi / 2) ∨ (Real.pi / 2) < θ.toReal)
: ↑(Real.arctan θ.tan) + ↑Real.pi = θ := by
  rw [←Real.Angle.tan_toReal]
  let θr := θ.toReal
  --
  -- From h_range, we know either:  θr < -π/2  or  π/2 < θr
  have all_range := Real.Angle.abs_toReal_le_pi
  --
  -- From all_range, we know:  |θr| ≤ π
  by_cases h_sign : θr ≥ 0
  --
  · -- θ nonnegative

    -- From h_sign, we know:  0 < θr
    have h_sign : 0 ≤ θr := h_sign.ge
    --
    -- Which means h_range reduces to:  π/2 < θr
    have h_lbnd : (Real.pi / 2) < θr := by
      cases h_range
      · case inl h =>
        have : θr < 0 := lt_of_lt_of_le h (by grind : -(Real.pi / 2) ≤ 0)
        have h : ¬0 ≤ θr := by linarith
        contradiction
      · case inr h => exact h
    --
    -- Combined with all_range gives:  π/2 < θr ≤ π
    have h_ubnd := all_range θ
    rw [abs_of_nonneg h_sign] at h_ubnd
    --
    -- So for θ₁:=θr-π, we know:  -π/2 < θ₁ ≤ 0    Which is safe under tangent
    let θ₁ : ℝ := θ.toReal - Real.pi
    have h_θ₁ : θ₁ + Real.pi = θ := by unfold θ₁; rw [←Real.Angle.coe_add]; simp
    have h_θ₁_int : θ.toReal = θ₁ + (1 : ℝ) * Real.pi := by linarith -- Keep *1 for tangent lemma
    have h_θ₁_int : θ.toReal = θ₁ + (1 : ℤ) * Real.pi := by norm_cast
    rw [h_θ₁_int]
    rw [Real.tan_add_int_mul_pi θ₁ 1]
    --
    -- Which gives us our range:
    have h_θ₁_lbnd : -(Real.pi / 2) < θ₁ := by linarith
    have h_θ₁_ubnd : θ₁ < Real.pi / 2 := by linarith
    --
    -- With which we can eliminate arctan and tan:
    rw [Real.arctan_tan h_θ₁_lbnd h_θ₁_ubnd]
    --
    exact h_θ₁
    --
  · -- θ negative

    -- From h_sign, we know:  θr < 0
    have h_sign : θr < 0 := not_le.mp h_sign
    --
    -- Which means h_range reduces to:  θr < -π/2
    have h_range : θr < -(Real.pi / 2) := by
      cases h_range
      · case inl h => exact h
      · case inr h =>
        have h : 0 ≤ θr := (lt_of_lt_of_le (by grind : 0 < Real.pi / 2) (le_of_lt h)).le
        contradiction
    --
    -- And all_range reduces to:  -θr ≤ π  =>  θr ≥ -π  =>  -π ≤ θr
    have h_ubnd := all_range θ
    rw [abs_of_neg h_sign] at h_ubnd
    have h_lbnd : -Real.pi ≤ θr := by linarith
    --
    -- Combined with h_range gives:  -π ≤ θr < -π/2
    have h_ubnd : θr < -(Real.pi / 2) := by linarith
    --
    -- So for θ₁:=θr+π, we know:  0 ≤ θ₁ < π/2    Which is safe under tangent
    let θ₁ := θ.toReal + Real.pi
    have h_θ₁ : θ.toReal = θ₁ - Real.pi := by linarith
    rw [h_θ₁]
    --
    -- have h_θ₁ : θ₁ + Real.pi = θ := by unfold θ₁; rw [←Real.Angle.coe_add]; simp

    -- Which gives us our range:
    have h_θ₁_lbnd : 0 ≤ θ₁ := by linarith
    have h_θ₁_ubnd : θ₁ < Real.pi / 2 := by linarith
    --
    -- With which we can eliminate arctan and tan:
    rw [Real.tan_sub_pi θ₁]
    rw [Real.arctan_tan (by linarith : -(Real.pi / 2) < θ₁) h_θ₁_ubnd]
    rw [Real.Angle.coe_add]
    --
    rw [add_assoc]
    rw [Real.Angle.coe_pi_add_coe_pi]
    simp

lemma cos_iff_range {θ : Real.Angle} (hn0 : θ.cos ≠ 0)
: ((if θ.cos < 0 then ↑(Real.arctan θ.tan) + ↑Real.pi else ↑(Real.arctan θ.tan)) : Real.Angle) = θ
:= by
  by_cases h_cos_sign : θ.cos < 0
  --
  · case pos => -- cosθ is negative
    simp only [h_cos_sign, ↓reduceIte]
    have h_range : θ.toReal < -(Real.pi / 2) ∨ Real.pi / 2 < θ.toReal := by
      have h_range := Real.Angle.cos_neg_iff_pi_div_two_lt_abs_toReal.mp h_cos_sign
      by_cases h_sign : θ.toReal < 0
      · rw [abs_of_neg h_sign, lt_neg] at h_range
        exact Or.inl h_range
      · rw [abs_of_nonneg (le_of_not_gt h_sign)] at h_range
        exact Or.inr h_range
    exact angle_arctan_tan_pi h_range
  -- End pos
  · case neg => -- cosθ is positive (0 is handled by hn0)
    simp only [h_cos_sign, ↓reduceIte]
    have h_cos_sign : 0 < θ.cos := by
      simp only [not_lt] at h_cos_sign
      have h_cos_sign_wk := (le_iff_lt_or_eq.mp h_cos_sign).resolve_right
      exact h_cos_sign_wk (Ne.symm hn0)
    have h_range : -(Real.pi / 2) < θ.toReal ∧ θ.toReal < Real.pi / 2 := by
      have h_range := (@Real.Angle.cos_pos_iff_abs_toReal_lt_pi_div_two θ).mp h_cos_sign
      by_cases h_sign : θ.toReal < 0
      · rw [abs_of_neg h_sign, neg_lt] at h_range
        exact And.intro h_range (by linarith)
      · rw [abs_of_nonneg (le_of_not_gt h_sign)] at h_range
        exact And.intro (by linarith) h_range
    exact angle_arctan_tan h_range
  -- End neg

theorem to_from_angle : to_angle (from_angle θ) = θ := by
  unfold from_angle
  unfold to_angle
  -- θ = π/2
  if h_π2: θ.toReal = Real.pi / 2 then
    rw [ite_eq_left h_π2, ←h_π2]
    simp only [↓reduceIte, ge_iff_le, zero_le_one, Real.Angle.coe_toReal]
  -- θ = -π/2
  else if h_mπ2 : θ.toReal = -Real.pi / 2 then
    rw [ite_eq_right h_π2, ite_eq_left h_mπ2]
    simp only [↓reduceIte, ge_iff_le, Left.nonneg_neg_iff]
    rw [ite_eq_right (by simp), ←h_mπ2]
    simp only [Real.Angle.coe_toReal]
  -- θ ≠ π/2+kπ
  else
    rw [ite_eq_right h_π2, ite_eq_right h_mπ2]
    simp only [Real.Angle.toReal_eq_pi_div_two_iff, Real.Angle.toReal_eq_neg_pi_div_two_iff,
      ge_iff_le] at h_π2 h_mπ2 ⊢
    have hn0 : θ.cos ≠ 0 := by
      have h := And.intro h_π2 h_mπ2
      rw [←not_or] at h
      have h0iffπ := Iff.not (@Real.Angle.cos_eq_zero_iff θ)
      exact Iff.mpr h0iffπ h
    rw [ite_eq_right hn0]
    rw [←Real.Angle.tan_eq_sin_div_cos]
    exact cos_iff_range hn0

end Dir
