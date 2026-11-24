module

public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.RingTheory.Valuation.Integral

/-!
# Integral elements have norm at most one

A Mathlib-only lemma that was proved separately in many modules.
-/

@[expose] public section

namespace Formalism.SharedLemmas

/-- An element of an ultrametric normed field that is integral over `ℤ` has norm at most one. -/
theorem norm_le_one_of_isIntegral {K : Type*} [NormedField K] [IsUltrametricDist K] {x : K}
    (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := K)).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := K))).mem_of_integral h1
  have h3 : NormedField.valuation x ≤ 1 := h2
  rw [NormedField.valuation_apply] at h3
  exact_mod_cast h3

end Formalism.SharedLemmas
