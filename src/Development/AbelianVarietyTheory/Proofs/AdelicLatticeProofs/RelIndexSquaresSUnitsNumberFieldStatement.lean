module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RelIndexSquaresSUnitsNumberField
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.relIndex_squares_sUnitsNumberField : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), (sqs (sUnits F S)).relIndex (sUnits F S) = 2 ^ (S.card + Fintype.card (InfinitePlace F)) := by
  first | exact @GlobalTheory.QNorm.relIndex_sqs_sUnits | exact GlobalTheory.QNorm.relIndex_sqs_sUnits | (intros; apply GlobalTheory.QNorm.relIndex_sqs_sUnits <;> assumption)
