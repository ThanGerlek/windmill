-- Let S be a set of at least two points in the plane.
-- Assume that no three points are collinear.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

structure Point where
  x : ℝ
  y : ℝ

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

-- IsSameLine theorems

def IsSameLine (l₁ l₂ : DirectedLineRep) : Prop :=
  ∀ (p : Point), p ∈ l₁ ↔ p ∈ l₂

theorem sameline_refl : ∀ (x : DirectedLineRep), x.IsSameLine x := by
  -- unfold DirectedLineRep.IsSameLine
  intro x p
  simp

theorem sameline_symm : ∀ {x y : DirectedLineRep}, x.IsSameLine y → y.IsSameLine x := by
  -- unfold DirectedLineRep.IsSameLine
  intro x y h p
  rw [iff_comm_eq]
  exact h p

theorem sameline_trans : ∀ {x y z : DirectedLineRep},
  x.IsSameLine y → y.IsSameLine z → x.IsSameLine z := by
  -- unfold DirectedLineRep.IsSameLine
  intro x y z hxy hyz p
  rw [hxy, hyz]

-- Respects theorems

theorem mem_respects (l₁ l₂ : DirectedLineRep)
  (h : l₁.IsSameLine l₂) :
  (p ∈ l₁) = (p ∈ l₂) := by
  -- unfold IsSameLine at h
  simp only [eq_iff_iff]
  exact h p


instance : Setoid DirectedLineRep where
  r := DirectedLineRep.IsSameLine
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
    (fun l₁ l₂ h => DirectedLineRep.mem_respects l₁ l₂ h)
    l

instance : Membership Point DirectedLine where mem := mem

def colinear (p q r : Point) := ∃ (l : DirectedLine), p∈l ∧ q∈l ∧ r∈l

end DirectedLine

-- #min_imports
