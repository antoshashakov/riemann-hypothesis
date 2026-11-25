module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SUnitMemGlobalNormOfMemLocalNorms
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.sUnit_mem_globalNorm_of_mem_localNorms : ∀ (F : Type) [Field F] [NumberField F] (δ : Fˣ) (S : Finset (HeightOneSpectrum (𝓞 F))), admitted F S → δ ∈ sUnits F S → ¬ IsSquare (δ : F) → ∀ x ∈ sUnits F S, x ∈ locNorm F δ S → x ∈ normSub (RingHom.id F) (δ : F) := by
  first | exact @GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm | exact GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm | (intros; apply GlobalTheory.QNorm.sUnit_mem_normSub_of_mem_locNorm <;> assumption)
