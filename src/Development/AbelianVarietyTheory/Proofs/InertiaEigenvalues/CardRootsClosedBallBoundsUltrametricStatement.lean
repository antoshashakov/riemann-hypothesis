module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardRootsClosedBallBoundsUltrametric
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open Polynomial
open Classical

theorem _root_.GlobalTheory.T.card_roots_closedBall_bounds_ultrametric : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [IsAlgClosed K] (f : K[X]) (ρ : ℝ) (d : ℕ), 0 < ρ → f.coeff d ≠ 0 → ((∀ j, ‖f.coeff j‖ * ρ ^ j ≤ ‖f.coeff d‖ * ρ ^ d) → d ≤ Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ)) ∧ ((∀ j, d < j → ‖f.coeff j‖ * ρ ^ j < ‖f.coeff d‖ * ρ ^ d) → Multiset.card (f.roots.filter fun z => ‖z‖ ≤ ρ) ≤ d) := by
  first | exact @GlobalTheory.card_roots_le_radius_bounds | exact GlobalTheory.card_roots_le_radius_bounds | (intros; apply GlobalTheory.card_roots_le_radius_bounds <;> assumption)
