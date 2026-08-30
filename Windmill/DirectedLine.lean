-- Let S be a set of at least two points in the plane.
-- Assume that no three points are collinear.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Windmill.Defs

-- DirectedLineRep

structure DirectedLineRep where
  pt : Point
  θ : Real.Angle

namespace DirectedLineRep

-- Membership

def mem (l : DirectedLineRep) (p : Point) : Prop :=
  ∃ (s : ℝ),
      (l.pt.x + s*(Real.Angle.cos l.θ) = p.x)
    ∧ (l.pt.y + s*(Real.Angle.sin l.θ) = p.y)

instance : Membership Point DirectedLineRep where mem := mem

theorem pt_is_mem (l : DirectedLineRep) : l.pt ∈ l := by use 0; simp

-- equiv theorems

def equiv (l₁ l₂ : DirectedLineRep) : Prop :=
  ∀ (p : Point), p ∈ l₁ ↔ p ∈ l₂

theorem sameline_refl : ∀ (x : DirectedLineRep), x.equiv x := by intro a p; simp

theorem sameline_symm : ∀ {x y : DirectedLineRep}, x.equiv y → y.equiv x := by
  intro x y h p
  rw [iff_comm_eq]
  exact h p

theorem sameline_trans : ∀ {x y z : DirectedLineRep},
  x.equiv y → y.equiv z → x.equiv z := by
  intro x y z hxy hyz p
  rw [hxy, hyz]

theorem sameLine_pt_is_mem (l₁ l₂ : DirectedLineRep) (h : l₁.equiv l₂) : l₁.pt ∈ l₂ := by
  let h := h l₁.pt
  let h₁ := pt_is_mem l₁
  exact Iff.mp h h₁

-- rotate theorems

noncomputable def rotate (l : DirectedLineRep) (θ : Real.Angle) : DirectedLineRep :=
  mk l.pt (l.θ + θ)

@[simp]
theorem rotate_pt : ∀ {θ}, ((l : DirectedLineRep).rotate θ).pt = l.pt := by
  unfold rotate; simp

@[simp]
theorem rotate_θ : ∀ {θ}, ((l : DirectedLineRep).rotate θ).θ = l.θ + θ := by
  unfold rotate; simp

-- Instance Setoid

instance : Setoid DirectedLineRep where
  r := equiv
  iseqv := by
    constructor
    · exact sameline_refl
    · exact sameline_symm
    · exact sameline_trans

end DirectedLineRep

-- DirectedLine

def DirectedLine := Quotient (inferInstance : Setoid DirectedLineRep)

namespace DirectedLine

def mem (l : DirectedLine) (p : Point) : Prop :=
  Quotient.lift
    (fun l => DirectedLineRep.mem l p)
    (by
      intro a b h
      change ∀ (p : Point), a.mem p ↔ b.mem p at h
      rw [←iff_eq_eq]
      exact h p)
    l

instance : Membership Point DirectedLine where mem := mem

def colinear (p q r : Point) := ∃ (l : DirectedLine), p∈l ∧ q∈l ∧ r∈l

end DirectedLine

#min_imports
