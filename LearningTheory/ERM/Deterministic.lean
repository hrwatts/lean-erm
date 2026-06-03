import Mathlib.Data.Real.Basic
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic

namespace LearningTheory
namespace ERM

universe u

/-- `x` is a `δ`-approximate minimizer of `f` over the whole domain. -/
def ApproxMin {α : Type u} (f : α → ℝ) (x : α) (δ : ℝ) : Prop :=
  ∀ y, f x ≤ f y + δ

/--
Deterministic approximate-minimizer transfer.

If `fhat` is uniformly within `ε` of `f`, and `x` is a `δ`-approximate
minimizer of `fhat`, then `x` is a `(2ε + δ)`-approximate minimizer of `f`.

This is the deterministic algebraic core used in ERM oracle inequalities.
It does not prove any probabilistic uniform-deviation bound.
-/
theorem le_of_abs_sub_le_of_forall_le_add
    {α : Type u}
    (f fhat : α → ℝ)
    (x : α)
    (ε δ : ℝ)
    (hdev : ∀ y, |fhat y - f y| ≤ ε)
    (hmin : ∀ y, fhat x ≤ fhat y + δ) :
    ∀ y, f x ≤ f y + 2 * ε + δ := by
  intro y
  have hx_abs : |fhat x - f x| ≤ ε := hdev x
  have hy_abs : |fhat y - f y| ≤ ε := hdev y
  have hx_lower : -ε ≤ fhat x - f x := (abs_le.mp hx_abs).1
  have hy_upper : fhat y - f y ≤ ε := (abs_le.mp hy_abs).2
  have hx : f x ≤ fhat x + ε := by linarith
  have hy : fhat y ≤ f y + ε := by linarith
  have hm : fhat x ≤ fhat y + δ := hmin y
  linarith

/--
Exact-minimizer version of `le_of_abs_sub_le_of_forall_le_add`.

This is the common ERM case where `x` exactly minimizes the surrogate objective.
-/
theorem le_of_abs_sub_le_of_forall_le
    {α : Type u}
    (f fhat : α → ℝ)
    (x : α)
    (ε : ℝ)
    (hdev : ∀ y, |fhat y - f y| ≤ ε)
    (hmin : ∀ y, fhat x ≤ fhat y) :
    ∀ y, f x ≤ f y + 2 * ε := by
  intro y
  have h := le_of_abs_sub_le_of_forall_le_add
    f fhat x ε 0 hdev (by intro z; simpa using hmin z) y
  linarith

example
    {α : Type u}
    (R Rhat : α → ℝ)
    (hhat : α)
    (ε δ : ℝ)
    (hdev : ∀ h, |Rhat h - R h| ≤ ε)
    (herm : ∀ h, Rhat hhat ≤ Rhat h + δ) :
    ∀ h, R hhat ≤ R h + 2 * ε + δ := by
  exact le_of_abs_sub_le_of_forall_le_add R Rhat hhat ε δ hdev herm

example
    {α : Type u}
    (R Rhat : α → ℝ)
    (hhat : α)
    (ε : ℝ)
    (hdev : ∀ h, |Rhat h - R h| ≤ ε)
    (herm : ∀ h, Rhat hhat ≤ Rhat h) :
    ∀ h, R hhat ≤ R h + 2 * ε := by
  exact le_of_abs_sub_le_of_forall_le R Rhat hhat ε hdev herm

variable {H : Type*}

/-- Uniform additive deviation between empirical risk `Rhat` and population risk `R`. -/
def UniformDeviationLe (R Rhat : H → ℝ) (ε : ℝ) : Prop :=
  ∀ h : H, |Rhat h - R h| ≤ ε

/-- `hhat` is an `α`-approximate empirical risk minimizer for `Rhat`. -/
def ApproxERM (Rhat : H → ℝ) (hhat : H) (α : ℝ) : Prop :=
  ApproxMin Rhat hhat α

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
  simpa [UniformDeviationLe, ApproxERM] using
    le_of_abs_sub_le_of_forall_le_add R Rhat hhat ε α hdev herm

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
  have hcomp : ∀ h : H, R hhat ≤ R h + (2 * ε + α) := by
    intro h
    have hh : R hhat ≤ R h + 2 * ε + α :=
      approxERM_oracle_IsGLB_empirical hdev hglbRhat herm h
    linarith
  exact comparator_to_IsGLB_population hglbR hcomp

end ERM
end LearningTheory