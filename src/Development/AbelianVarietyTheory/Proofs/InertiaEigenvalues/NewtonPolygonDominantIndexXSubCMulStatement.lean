module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NewtonPolygonDominantIndexXSubCMul
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Polynomial

theorem _root_.GlobalTheory.T.newtonPolygon_dominant_index_X_sub_C_mul : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ), 0 < ρ → ρ < ‖a‖ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) → (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) → (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff d‖ * ρ ^ d) ∧ ∀ j, d < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j < ‖((X - C a) * g).coeff d‖ * ρ ^ d := by
  first | exact @GlobalTheory.newton_step_root_outside_disc | exact GlobalTheory.newton_step_root_outside_disc | (intros; apply GlobalTheory.newton_step_root_outside_disc <;> assumption)
