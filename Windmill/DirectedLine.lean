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

lemma unique_angle_if_shared_root_and_point {l₁ l₂ : DirectedLineRep} {p : Point}
(h_e_pt : l₁.pt = l₂.pt) (h_p_ne : p ≠ l₁.pt) (h_p_mem : p ∈ l₁ ∧ p ∈ l₂) : l₁.θ = l₂.θ := by
  sorry

theorem unique_line_with_two_points {l₁ l₂ : DirectedLineRep} {p q : Point} (h_p_ne_q : p ≠ q)
(h_pq_in_1 : p ∈ l₁ ∧ q ∈ l₁) (h_pq_in_2 : p ∈ l₂ ∧ q ∈ l₂) : l₁.equiv l₂ := by
  -- l₁p : line with angle 1 and point p
  -- l₁  -?>  l₁p  -?>  l₁q  -?>  l₂q  -?>  l₂
  let l₁p := DirectedLineRep.mk_pt_angle p l₁.θ
  have h_1e1p : l₁.equiv l₁p := pt_independence h_pq_in_1.left
  suffices l₁p.equiv l₂ by
    exact sameline_trans h_1e1p this
  -- l₁ → l₁p  -?>  l₁q  -?>  l₂q  -?>  l₂
  let l₂q := DirectedLineRep.mk_pt_angle q l₂.θ
  have h_2qe2 : l₂q.equiv l₂ := by
    have h : l₂.equiv l₂q := pt_independence h_pq_in_2.right
    symm; exact h
  suffices l₁p.equiv l₂q by
    exact sameline_trans this h_2qe2
  -- l₁ → l₁p  -?>  l₁q  -?>  l₂q → l₂
  let l₁q := DirectedLineRep.mk_pt_angle q l₁.θ
  have h_q_in_l1p : q ∈ l₁p := by
    have h := h_pq_in_1.right
    rw [equiv_r h_1e1p] at h
    exact h
  have h : l₁p.equiv l₁q := pt_independence h_q_in_l1p
  suffices l₁q.equiv l₂q by exact sameline_trans h this
  -- l₁ → l₁p → l₁q  -?>  l₂q → l₂
  suffices l₁.θ = l₂.θ by
    unfold l₁q l₂q
    rw[this]
  -- l₁ → l₁p → l₁q → l₂q → l₂, assuming θ₁=θ₂
  -- Build args for unique_angle_if_shared_root_and_point
  apply @unique_angle_if_shared_root_and_point l₁q l₂q p
  · trivial
  · exact h_p_ne_q
  · -- p ∈ l₁q ∧ p ∈ l₂q
    have h₁ : p ∈ l₁q := by rw [←equiv_r h, ←equiv_r h_1e1p]; exact h_pq_in_1.left
    have h₂ : p ∈ l₂q := by rw [equiv_r h_2qe2]; exact h_pq_in_2.left
    exact And.intro h₁ h₂

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

-- colinearity

def colinear (p q r : Point) (_hpq : p ≠ q) (_hqr : q ≠ r) (_hpr : p ≠ r) :=
  ∃ l : DirectedLine, p∈l ∧ q∈l ∧ r∈l

def fin_colinear (p q r : Point) (hpq : p ≠ q) (hqr : q ≠ r) (hpr : p ≠ r) :=
  let ⟨lpq, _⟩ := DirectedLine.mk_pt_pt p q hpq
  let ⟨lqr, _⟩ := DirectedLine.mk_pt_pt q r hqr
  let ⟨lpr, _⟩ := DirectedLine.mk_pt_pt p r hpr
  (p ∈ lqr) ∨ (q ∈ lpr) ∨ (r ∈ lpq)

lemma colinear_if_fin_colinear {p q r : Point} {hpq : p ≠ q} {hqr : q ≠ r} {hpr : p ≠ r} :
fin_colinear p q r hpq hqr hpr → colinear p q r hpq hqr hpr := by
  unfold colinear fin_colinear
  let ⟨lpq, hlpq⟩ := DirectedLine.mk_pt_pt p q hpq
  let ⟨lqr, hlqr⟩ := DirectedLine.mk_pt_pt q r hqr
  let ⟨lpr, hlpr⟩ := DirectedLine.mk_pt_pt p r hpr
  intro h
  change p ∈ lqr ∨ q ∈ lpr ∨ r ∈ lpq at h
  rcases h with h1 | h2 | h3
  · use lqr
  · use lpr
    exact And.intro (hlpr.left) (And.intro h2 hlpr.right)
  · use lpq
    exact And.intro (hlpq.left) (And.intro hlpq.right h3)

lemma fin_colinear_if_colinear {p q r : Point} {hpq : p ≠ q} {hqr : q ≠ r} {hpr : p ≠ r} :
colinear p q r hpq hqr hpr → fin_colinear p q r hpq hqr hpr := by
  unfold colinear fin_colinear
  simp only [forall_exists_index, and_imp]
  let ⟨lpq, hlpq⟩ := DirectedLine.mk_pt_pt p q hpq
  let ⟨lqr, hlqr⟩ := DirectedLine.mk_pt_pt q r hqr
  let ⟨lpr, hlpr⟩ := DirectedLine.mk_pt_pt p r hpr
  intro l hlp hlq hlr
  sorry  -- Requires uniqueness of two points defining a line

theorem fin_colinear_iff_colinear {p q r : Point} {hpq : p ≠ q} {hqr : q ≠ r} {hpr : p ≠ r} :
colinear p q r hpq hqr hpr ↔ fin_colinear p q r hpq hqr hpr :=
  Iff.intro fin_colinear_if_colinear colinear_if_fin_colinear

end DirectedLine

#min_imports
