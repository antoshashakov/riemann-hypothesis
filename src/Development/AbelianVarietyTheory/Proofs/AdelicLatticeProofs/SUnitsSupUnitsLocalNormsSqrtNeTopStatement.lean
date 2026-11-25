module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitsSupUnitsLocalNormsSqrtNeTop
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.sUnits_sup_unitsLocalNormsSqrt_ne_top : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → sUnits F S ⊔ locNorm F δ S ≠ ⊤ := by
  first | exact @GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top | exact GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top | (intros; apply GlobalTheory.QNorm.sUnits_sup_locNorm_ne_top <;> assumption)
