module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WindowAroundLastMaxNullSequence
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.window_around_last_max_null_sequence : ∀ (β : ℤ → ℝ) (c : ℝ) (h : ℕ), 0 < c → (∀ k, 0 ≤ β k) → (∃ k, β k ≠ 0) → Filter.Tendsto β Filter.cofinite (nhds 0) → ∃ (D E M : ℕ), h ≤ D ∧ M + h ≤ E ∧ 0 < β ((M + h : ℕ) - D) ∧ (∀ k, β k ≤ β ((M + h : ℕ) - D)) ∧ (∀ k, ((M + h : ℕ) : ℤ) - D < k → β k < β ((M + h : ℕ) - D)) ∧ ∀ k : ℤ, (k < -(D : ℤ) ∨ (E : ℤ) - D < k) → β k ≤ c * β ((M + h : ℕ) - D) := by
  first | exact @GlobalTheory.window_around_last_max | exact GlobalTheory.window_around_last_max | (intros; apply GlobalTheory.window_around_last_max <;> assumption)
