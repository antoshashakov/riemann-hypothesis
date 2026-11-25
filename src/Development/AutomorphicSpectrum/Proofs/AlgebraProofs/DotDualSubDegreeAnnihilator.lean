module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Development.WeilBound.CoreStatements.HodgeTatePoints.DegLeOfEquiv
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open GlobalTheory.CompanionTheory.Ar.Crv

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem subDeg_dotDual_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W :=
  PositivityTheory.HtPt.Ch.subdeg_orth

end GlobalTheory.CompanionTheory.Ar.Crv
