module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsNumberFieldFg
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.sUnitsNumberField_fg : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))), Group.FG (sUnits F S) := by
  first | exact @GlobalTheory.QNorm.sUnits_fg | exact GlobalTheory.QNorm.sUnits_fg | (intros; apply GlobalTheory.QNorm.sUnits_fg <;> assumption)
