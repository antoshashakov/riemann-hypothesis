module

public import Mathlib.RingTheory.MvPowerSeries.Derivative
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PderivSubstChainRule
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

theorem _root_.GlobalTheory.T.pderiv_subst_chain_rule :
    ∀ {R σ τ : Type} [CommRing R] [Fintype σ] [Fintype τ] (a : σ → MvPowerSeries τ R),
      (∀ s, constantCoeff (a s) = 0) → ∀ (f : MvPowerSeries σ R) (k : τ),
        pderiv (R := R) k (subst a f) = ∑ j, subst a (pderiv (R := R) j f) * pderiv (R := R) k (a j) := by
  exact @GlobalTheory.PSChain.pderiv_subst_chain
