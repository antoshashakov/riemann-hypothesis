module

public import Mathlib.Order.Interval.Finset.Nat
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

namespace Formalism.ZetaNonvanishing.ARCV

open Polynomial

theorem range_sdiff_range (H : ℕ) : Finset.range (2 * H) \ Finset.range H = Finset.Ico H (2 * H) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico]
  omega

end Formalism.ZetaNonvanishing.ARCV
