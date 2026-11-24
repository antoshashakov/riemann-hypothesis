module

public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualOfCompatibleModPow
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.existsUnique_dual_of_compatible_mod_pow_of_adicComplete : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O) [IsAdicComplete (Ideal.span {a}) O] (u : ∀ n : ℕ, M →ₗ[O] O ⧸ Ideal.span {a ^ n}), (∀ n w (x : O), u (n + 1) w = Ideal.Quotient.mk _ x → u n w = Ideal.Quotient.mk _ x) → ∃! l : Module.Dual O M, ∀ n w, Ideal.Quotient.mk _ (l w) = u n w := by
  first | exact @GlobalTheory.PDiv.exists_unique_dual_of_compatible_mod_pow | exact GlobalTheory.PDiv.exists_unique_dual_of_compatible_mod_pow | (intros; apply GlobalTheory.PDiv.exists_unique_dual_of_compatible_mod_pow <;> assumption)
