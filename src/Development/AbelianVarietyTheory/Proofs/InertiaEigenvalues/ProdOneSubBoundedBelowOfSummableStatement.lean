module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOneSubBoundedBelowOfSummable
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

theorem _root_.GlobalTheory.T.prod_one_sub_bounded_below_of_summable : ∀ (ι : Type) (s : ι → ℝ), (∀ v, 0 ≤ s v) → (∀ v, s v < 1) → Summable s → ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ι, δ ≤ ∏ v ∈ S, (1 - s v) := by
  first | exact @GlobalTheory.prod_one_sub_bounded_below | exact GlobalTheory.prod_one_sub_bounded_below | (intros; apply GlobalTheory.prod_one_sub_bounded_below <;> assumption)
