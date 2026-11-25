module

public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfPerfectOfDvdSubAdicSeparated
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open scoped NNReal

theorem _root_.GlobalTheory.T.ringHom_eq_of_perfect_of_dvd_sub_adicSeparated : ∀ (l : ℕ) [Fact l.Prime] (R O : Type) [CommRing R] [CharP R l] [PerfectRing R l] [CommRing O] [CharP O l] (x : O) (e : ℕ), 0 < e → IsHausdorff (Ideal.span {x}) O → ∀ ψ ψ' : R →+* O, (∀ y, x ^ e ∣ ψ y - ψ' y) → ψ = ψ' := by
  first | exact @GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | exact GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub | (intros; apply GlobalTheory.ringHom_eq_of_perfect_of_dvd_sub <;> assumption)
