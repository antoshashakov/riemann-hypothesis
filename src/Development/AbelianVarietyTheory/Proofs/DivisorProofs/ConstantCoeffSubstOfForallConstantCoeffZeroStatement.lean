module

public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantCoeffSubstOfForallConstantCoeffZero
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.constantCoeff_subst_of_forall_constantCoeff_zero : ∀ (R : Type) [CommRing R] (σ τ : Type) [Finite σ] (a : σ → MvPowerSeries τ R), (∀ i, constantCoeff (a i) = 0) → ∀ g : MvPowerSeries σ R, constantCoeff (subst a g) = constantCoeff g := by
  first | exact @GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | exact GlobalTheory.constantCoeff_subst_of_constantCoeff_zero | (intros; apply GlobalTheory.constantCoeff_subst_of_constantCoeff_zero <;> assumption)
