-- Let S be a set of at least two points in the plane.
-- Assume that no three points are collinear.

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Windmill.Defs

-- DirectedLineRep

structure DirectedLineRep where
  pt : Point
  θ : Real.Angle

namespace DirectedLineRep

noncomputable def dir (l : DirectedLineRep) : Point := Point.fromAngle l.θ

-- Membership

def mem (l : DirectedLineRep) (p : Point) : Prop :=
  ∃ s : ℝ, l.pt + s • l.dir = p

instance : Membership Point DirectedLineRep where mem := mem

theorem pt_is_mem (l : DirectedLineRep) : l.pt ∈ l := by use 0; simp

-- constructors

def mk_pt_angle := mk

noncomputable def mk_pt_pt (p q : Point) (h : p ≠ q) : {l : DirectedLineRep // p∈l ∧ q∈l} :=
  let θ : Real.Angle := p.oangle (q - p)
  let l : DirectedLineRep := DirectedLineRep.mk p θ
  have h₁ : p∈l := pt_is_mem l
  have h₂ : q∈l := by
    have h := Point.inner_eq_norm_mul_norm_mul_cos_oangle p q
    change DirectedLineRep.mem l q
    unfold DirectedLineRep.mem
    simp [l]

    sorry
  ⟨l, And.intro h₁ h₂⟩

-- equiv theorems

def equiv (l₁ l₂ : DirectedLineRep) : Prop :=
  ∀ (p : Point), p ∈ l₁ ↔ p ∈ l₂

theorem equiv_r {l₁ l₂ : DirectedLineRep} (h : l₁.equiv l₂) : ∀ (p : Point), p ∈ l₁ ↔ p ∈ l₂ := by
  intro p; unfold equiv at h; exact h p

@[refl]
theorem sameline_refl : ∀ (x : DirectedLineRep), x.equiv x := by intro a p; simp

@[symm]
theorem sameline_symm : ∀ {x y : DirectedLineRep}, x.equiv y → y.equiv x := by
  intro x y h p
  rw [iff_comm_eq]
  exact h p

@[trans]
theorem sameline_trans : ∀ {x y z : DirectedLineRep},
  x.equiv y → y.equiv z → x.equiv z := by
  intro x y z hxy hyz p
  rw [hxy, hyz]

theorem sameLine_pt_is_mem (l₁ l₂ : DirectedLineRep) (h : l₁.equiv l₂) : l₁.pt ∈ l₂ := by
  let h := h l₁.pt
  let h₁ := pt_is_mem l₁
  exact Iff.mp h h₁

-- For any p in l, a line made from p (with same θ) is equivalent to l.
theorem pt_independence {l : DirectedLineRep} {pt : Point} (h : pt ∈ l) : l.equiv (mk pt l.θ) := by
  sorry

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

instance instSetoidDirectedLineRep : Setoid DirectedLineRep where
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

def mk_pt_angle (p : Point) (θ : Real.Angle) : DirectedLine :=
  Quotient.mk _ (DirectedLineRep.mk_pt_angle p θ)

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

-- constructors

noncomputable def mk_pt_pt (p q : Point) (h : p ≠ q) : {l : DirectedLine // p∈l ∧ q∈l} :=
  let ⟨l, hl⟩ := DirectedLineRep.mk_pt_pt p q h
  ⟨Quotient.mk _ l, hl⟩

def colinear (p q r : Point) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :=
∃ l : DirectedLine, p∈l ∧ q∈l ∧ r∈l

end DirectedLine

#min_imports
