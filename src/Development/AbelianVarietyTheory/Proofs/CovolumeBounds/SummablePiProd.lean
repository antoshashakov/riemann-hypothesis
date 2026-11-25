module

import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Supplements.MathlibImports.AnalysisAndTactics
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.Algebra.InfiniteSum.Real

@[expose] public section

namespace GlobalTheory.SummablePiProd

universe u_1 u_2

theorem summable_pi_prod {ι : Type u_1} [inst : Fintype ι] {J : ι → Type u_2}
    {u : (i : ι) → J i → ℝ} (h0 : ∀ (i : ι) (j : J i), (0 : ℝ) ≤ u i j)
    (hs : ∀ (i : ι), Summable (u i)) :
    Summable fun (t : (i : ι) → J i) ↦ ∏ i : ι, u i (t i) := by
  apply GlobalTheory.summable_pi_prod_of_nonneg <;> assumption

end GlobalTheory.SummablePiProd
