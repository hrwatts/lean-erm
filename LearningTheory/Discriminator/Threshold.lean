import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Tactic

namespace LearningTheory
namespace Discriminator

universe u

/--
If a score `s` is uniformly within `ε` of a target score `η`, then the
threshold rules induced by `s` and `η` can disagree only where `η` is within
`ε` of the threshold.
-/
theorem threshold_disagreement_subset_boundary
    {α : Type u}
    (η s : α → ℝ)
    (ε : ℝ)
    (hε : 0 ≤ ε)
    (hclose : ∀ x, |s x - η x| ≤ ε) :
    {x | ((0 ≤ s x) ≠ (0 ≤ η x))} ⊆ {x | |η x| ≤ ε} := by
  have _ := hε
  intro x hx
  by_cases hs : 0 ≤ s x
  · have hη_not : ¬ 0 ≤ η x := by
      intro hη
      exact hx (propext ⟨fun _ => hη, fun _ => hs⟩)
    have hη_lt : η x < 0 := lt_of_not_ge hη_not
    have hdiff : s x - η x ≤ ε := (abs_le.mp (hclose x)).2
    have hnegη_le : -η x ≤ ε := by
      linarith
    simpa [Set.mem_setOf_eq, abs_of_neg hη_lt] using hnegη_le
  · have hs_lt : s x < 0 := lt_of_not_ge hs
    have hη : 0 ≤ η x := by
      by_contra hη_not
      exact hx (propext ⟨fun hs0 => False.elim (hs hs0), fun hη0 => False.elim (hη_not hη0)⟩)
    have hneg : -ε ≤ s x - η x := (abs_le.mp (hclose x)).1
    have hη_le : η x ≤ ε := by
      linarith
    simpa [Set.mem_setOf_eq, abs_of_nonneg hη] using hη_le

/--
If the target score `η x` is farther than `ε` from the threshold, then any
score `s` uniformly within `ε` of `η` induces the same threshold decision at
`x`.
-/
theorem threshold_agree_of_boundary_lt
    {α : Type u}
    (η s : α → ℝ)
    (ε : ℝ)
    (hε : 0 ≤ ε)
    (hclose : ∀ x, |s x - η x| ≤ ε)
    (x : α)
    (hmargin : ε < |η x|) :
    (0 ≤ s x) = (0 ≤ η x) := by
  by_contra hneq
  have hdisagree : ((0 ≤ s x) ≠ (0 ≤ η x)) := by
    exact hneq
  have hboundary : |η x| ≤ ε :=
    threshold_disagreement_subset_boundary η s ε hε hclose hdisagree
  linarith

/--
Measure version of `threshold_disagreement_subset_boundary`.
-/
theorem measure_threshold_disagreement_le_boundary
    {α : Type u}
    [MeasurableSpace α]
    (μ : MeasureTheory.Measure α)
    (η s : α → ℝ)
    (ε : ℝ)
    (hε : 0 ≤ ε)
    (hclose : ∀ x, |s x - η x| ≤ ε) :
    μ {x | ((0 ≤ s x) ≠ (0 ≤ η x))}
      ≤ μ {x | |η x| ≤ ε} := by
  apply MeasureTheory.measure_mono
  exact threshold_disagreement_subset_boundary η s ε hε hclose

end Discriminator
end LearningTheory
