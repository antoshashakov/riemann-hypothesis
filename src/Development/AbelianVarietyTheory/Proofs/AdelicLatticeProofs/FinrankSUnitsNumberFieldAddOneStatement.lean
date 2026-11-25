module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FinrankSUnitsNumberFieldAddOne
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.finrank_sUnitsNumberField_add_one : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), Module.finrank ℤ (Additive (sUnits F S)) + 1 = S.card + Fintype.card (InfinitePlace F) := by
  first | exact @GlobalTheory.QNorm.sUnits_rank | exact GlobalTheory.QNorm.sUnits_rank | (intros; apply GlobalTheory.QNorm.sUnits_rank <;> assumption)
