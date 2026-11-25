module

public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub
public import Mathlib.RingTheory.Ideal.Norm.AbsNorm
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IndexUnitsSquareUnderRingHomAdicCompletionLe
import Supplements.MathlibImports.AnalysisAndTactics

@[expose] public section

open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

theorem _root_.GlobalTheory.T.index_unitsSquareUnderRingHom_adicCompletion_le : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (e : ℕ), v.valuation F 2 = WithZero.exp (-(e : ℤ)) → (sqSub (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧ (sqSub (algebraMap F (v.adicCompletion F))).index ≤ 4 * Ideal.absNorm v.asIdeal ^ e := by
  first | exact @GlobalTheory.QNorm.index_sqSub_adicCompletion_le | exact GlobalTheory.QNorm.index_sqSub_adicCompletion_le | (intros; apply GlobalTheory.QNorm.index_sqSub_adicCompletion_le <;> assumption)
