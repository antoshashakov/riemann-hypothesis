module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.WeilBound.CoreStatements.SesquilinearFractions.UltrametricNormProdSubLt
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes

@[expose] public section

open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl

theorem norm_det_eq_of_entries_close : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M M' : Matrix I I A) (r : ℝ), 0 < r → (∀ a b, ‖M a b‖ ≤ r) → (∀ a b, ‖M' a b - M a b‖ < r) → ‖M.det‖ = r ^ Fintype.card I → ‖M'.det‖ = r ^ Fintype.card I :=
  @PositivityTheory.Xgf.ultrametric_det_norm_stable

end GlobalTheory.CompanionTheory.Ar.Fl
