-- Let S be a set of at least two points in the plane.
-- Assume that no three points are collinear.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle

structure Point where
  x : ℝ
  y : ℝ

structure DirectedLineRep where
  pt : Point
  θ : Real.Angle  -- modulo 360 rather than 180, to keep directed-ness

namespace DirectedLineRep

def mem (l : DirectedLineRep) (p : Point) : Prop :=
  ∃ (s : ℝ),
      (l.pt.x + (s*Real.Angle.cos l.θ) = p.x)
    ∧ (l.pt.y + (s*Real.Angle.sin l.θ) = p.y)

instance : Membership Point DirectedLineRep where mem := mem

def IsSameLine (l1 l2 : DirectedLineRep) : Prop :=
  ∀ (p : Point), p ∈ l1 ↔ p ∈ l2

end DirectedLineRep

instance : Setoid DirectedLineRep where
  r := DirectedLineRep.IsSameLine
  iseqv := by
    constructor
    · -- refl
      unfold DirectedLineRep.IsSameLine
      intro x p
      simp
    · -- symm
      unfold DirectedLineRep.IsSameLine
      intro x y h p
      rw [iff_comm_eq]
      exact h p
    · -- trans
      unfold DirectedLineRep.IsSameLine
      intro x y z hxy hyz p
      rw [hxy, hyz]

def DirectedLine := Quotient (inferInstance : Setoid DirectedLineRep)

-- Line properties defined on the representation

theorem mem_respects (l₁ l₂ : DirectedLineRep)
  (h : l₁.IsSameLine l₂) :
  (p ∈ l₁) = (p ∈ l₂) := by
  unfold DirectedLineRep.IsSameLine at h
  simp only [eq_iff_iff]
  exact h p

namespace DirectedLine

def mem (l : DirectedLine) (p : Point) : Prop :=
  Quotient.lift
    (fun l => p ∈ l)
    (fun l₁ l₂ h => mem_respects l₁ l₂ h)
    l

instance : Membership Point DirectedLine where mem := mem

end DirectedLine

def colinear (p q r : Point) := ∃ (l : DirectedLine), p∈l ∧ q∈l ∧ r∈l

-- #min_imports
