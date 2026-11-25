module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Valuation
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ProdAbsNormPowValuationTwoLe
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.prod_absNorm_pow_valuation_two_le : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (e : HeightOneSpectrum (𝓞 F) → ℕ), (∀ v ∈ S, v.valuation F 2 = WithZero.exp (-(e v : ℤ))) → ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ 2 ^ Module.finrank ℚ F := by
  first | exact @GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow | exact GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow | (intros; apply GlobalTheory.QNorm.prod_absNorm_pow_le_two_pow <;> assumption)
