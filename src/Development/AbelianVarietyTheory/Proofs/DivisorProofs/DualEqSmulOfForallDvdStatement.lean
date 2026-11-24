module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Dual.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualEqSmulOfForallDvd
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.KerIdealCompOfSurjective
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsCounitDerivationCounitComp
import Mathlib.RingTheory.MvPowerSeries.Basic

@[expose] public section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

theorem _root_.GlobalTheory.T.dual_eq_smul_of_forall_dvd' : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (a : O), (∀ x : O, a * x = 0 → x = 0) → ∀ l : Module.Dual O M, (∀ w, a ∣ l w) → ∃ l' : Module.Dual O M, l = a • l' := by
  first | exact @GlobalTheory.dual_eq_smul_of_forall_dvd | exact GlobalTheory.dual_eq_smul_of_forall_dvd | (intros; apply GlobalTheory.dual_eq_smul_of_forall_dvd <;> assumption)
