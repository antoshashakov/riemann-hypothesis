module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Completion
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsEqPowMulPthPowAdicCompletionUnit
import Supplements.MathlibImports.AnalysisAndTactics
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.SqSubLeNormSub

@[expose] public section

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

theorem _root_.GlobalTheory.T.exists_eq_pow_mul_pth_pow_adicCompletion_unit : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (x y : v.adicCompletion F), p.Prime → v.valuation F (p : F) = 1 → Valued.v x = 1 → Valued.v y = 1 → (∀ r : v.adicCompletion F, r ^ p ≠ x) → ∃ (k : ℕ) (r : v.adicCompletion F), y = x ^ k * r ^ p := by
  first | exact @GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit | exact GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit | (intros; apply GlobalTheory.CNorm.exists_eq_pow_mul_pow_of_unit <;> assumption)
