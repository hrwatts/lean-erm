import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

namespace LearningTheory
namespace ERM

variable {H : Type*}

/-- Uniform additive deviation between empirical risk `Rhat` and population risk `R`. -/
def UniformDeviationLe (R Rhat : H → ℝ) (ε : ℝ) : Prop :=
  ∀ h : H, |Rhat h - R h| ≤ ε

/-- `hhat` is an `α`-approximate empirical risk minimizer for `Rhat`. -/
def ApproxERM (Rhat : H → ℝ) (hhat : H) (α : ℝ) : Prop :=
  ∀ h : H, Rhat hhat ≤ Rhat h + α

/-- `hhat` has empirical risk within `α` of a chosen GLB value `rhatStar`. -/
def ApproxERMAtGLB (Rhat : H → ℝ) (hhat : H) (rhatStar α : ℝ) : Prop :=
  Rhat hhat ≤ rhatStar + α

/-- Left-side consequence of uniform deviation. -/
theorem uniformDeviation_population_le_empirical
    {R Rhat : H → ℝ} {ε : ℝ}
    (hdev : UniformDeviationLe R Rhat ε)
    (h : H) :
    R h ≤ Rhat h + ε := by
  have hdev' : |R h - Rhat h| ≤ ε := by
    simpa [abs_sub_comm] using hdev h
  have hle : R h - Rhat h ≤ ε := (abs_le.mp hdev').2
  linarith

theorem uniformDeviation_empirical_le_population
    {R Rhat : H → ℝ} {ε : ℝ}
    (hdev : UniformDeviationLe R Rhat ε)
    (h : H) :
    Rhat h ≤ R h + ε := by
  have hle : Rhat h - R h ≤ ε := (abs_le.mp (hdev h)).2
  linarith

/-- Deterministic oracle comparator bound from uniform deviation and approximate ERM. -/
theorem approxERM_oracle_comparator
    {R Rhat : H → ℝ} {hhat : H} {ε α : ℝ}
    (hdev : UniformDeviationLe R Rhat ε)
    (herm : ApproxERM Rhat hhat α) :
    ∀ h : H, R hhat ≤ R h + 2 * ε + α := by
  intro h
  have h1 : R hhat ≤ Rhat hhat + ε :=
    uniformDeviation_population_le_empirical hdev hhat
  have h2 : Rhat hhat ≤ Rhat h + α :=
    herm h
  have h3 : Rhat h ≤ R h + ε :=
    uniformDeviation_empirical_le_population hdev h
  linarith

/-- Convert an empirical GLB-gap assumption into comparator-form `ApproxERM`. -/
theorem approxERM_of_IsGLB_range
    {Rhat : H → ℝ} {hhat : H} {rhatStar α : ℝ}
    (hglb : IsGLB (Set.range Rhat) rhatStar)
    (herm : ApproxERMAtGLB Rhat hhat rhatStar α) :
    ApproxERM Rhat hhat α := by
  intro h
  have hlower : rhatStar ≤ Rhat h := hglb.1 ⟨h, rfl⟩
  unfold ApproxERMAtGLB at herm
  linarith

/-- Empirical GLB adapter composed with the deterministic comparator bound. -/
theorem approxERM_oracle_IsGLB_empirical
    {R Rhat : H → ℝ} {hhat : H} {rhatStar ε α : ℝ}
    (hdev : UniformDeviationLe R Rhat ε)
    (hglb : IsGLB (Set.range Rhat) rhatStar)
    (herm : ApproxERMAtGLB Rhat hhat rhatStar α) :
    ∀ h : H, R hhat ≤ R h + 2 * ε + α := by
  have hermComp : ApproxERM Rhat hhat α :=
    approxERM_of_IsGLB_range hglb herm
  exact approxERM_oracle_comparator hdev hermComp

/-- Convert a comparator inequality into a population-GLB inequality. -/
theorem comparator_to_IsGLB_population
    {R : H → ℝ} {hhat : H} {rStar c : ℝ}
    (hglb : IsGLB (Set.range R) rStar)
    (hcomp : ∀ h : H, R hhat ≤ R h + c) :
    R hhat ≤ rStar + c := by
  by_contra hnot
  have hlt : rStar + c < R hhat := lt_of_not_ge hnot
  let b : ℝ := R hhat - c
  have hb_lower : b ∈ lowerBounds (Set.range R) := by
    rw [mem_lowerBounds]
    intro y hy
    rcases hy with ⟨h, rfl⟩
    have hc : R hhat ≤ R h + c := hcomp h
    dsimp [b]
    linarith
  have hb_le : b ≤ rStar := hglb.2 hb_lower
  have hr_lt_b : rStar < b := by
    dsimp [b]
    linarith
  linarith

/-- Full deterministic oracle inequality using GLBs for population and empirical risks. -/
theorem approxERM_oracle_IsGLB
    {R Rhat : H → ℝ} {hhat : H} {rStar rhatStar ε α : ℝ}
    (hdev : UniformDeviationLe R Rhat ε)
    (hglbR : IsGLB (Set.range R) rStar)
    (hglbRhat : IsGLB (Set.range Rhat) rhatStar)
    (herm : ApproxERMAtGLB Rhat hhat rhatStar α) :
    R hhat ≤ rStar + (2 * ε + α) := by
  have hcomp : ∀ h : H, R hhat ≤ R h + (2 * ε + α) :=
    by
      intro h
      have hh : R hhat ≤ R h + 2 * ε + α :=
        approxERM_oracle_IsGLB_empirical hdev hglbRhat herm h
      linarith
  exact comparator_to_IsGLB_population hglbR hcomp

end ERM
end LearningTheory