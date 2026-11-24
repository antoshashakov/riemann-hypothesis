module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SummableVtQT
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MathlibImports

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.summable_vt_of_int : ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ (k : ℕ), k ≠ 0 → ∀ p : N.QT k, Summable (N.vt p.1.2) := by
  first | exact @GlobalTheory.Ex.summable_vt_QT | exact GlobalTheory.Ex.summable_vt_QT | (intros; apply GlobalTheory.Ex.summable_vt_QT <;> assumption)
